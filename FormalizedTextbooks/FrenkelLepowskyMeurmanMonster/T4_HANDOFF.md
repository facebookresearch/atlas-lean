# T4 (Monster order) — handoff, 2026-10-21

This file is the authoritative status of T4 at wrap-up. It is written so that a fresh agent
session can resume from this PR alone. The T4 sections of `README.md`, `GAPS.md` and
`HUMAN_REVIEW.md` were in-progress edits by an earlier session and are **stale**. Where they
disagree with this file, this file wins.

## TL;DR

- `Milestones.lean` is unchanged: `generated_group_order` (T4) still ends in `sorry`.
- **T4 is reduced, by a gated theorem, to coverage of nine global axis families:**

  ```lean
  -- GeneratedFeasibleAmbientT4Coverage.lean (gated, v2 stem /tmp/flm-cc-fbridge-t4)
  theorem generatedFeasibleAmbientT4_order_of_coverage
      (hcov : ∀ i ∈ ({3, 4, 5, 6, 7, 8, 9, 10, 11} : Finset (Fin 12)),
        GeneratedAxisGlobalTwelveFamilyCovered i) :
      Nat.card ↥G =
        2 ^ 46 * 3 ^ 20 * 5 ^ 9 * 7 ^ 6 * 11 ^ 2 * 13 ^ 3 *
        17 * 19 * 23 * 29 * 31 * 41 * 47 * 59 * 71
  ```

  The same module has `generatedFeasibleAmbientT4_order_of_families`, which takes nine named
  hypotheses `hfourth hfifth hsixth hseventh heighth hninth hrootEight htwelfth htenth`. Each
  family's closure theorem can be passed by name.
- **Closed:**
  - all 12 local orbit counts;
  - all 10 feasible classes and the feasible coverage bridge;
  - the global catalogue, with all twelve counts unconditional;
  - `FamilyCovered 0` (First), `1` (Octad) and `2` (Odd).
- **Open:** `FamilyCovered 3..11`. Each is reduced to explicit whole-vector *identification*
  equations. 125 of 279 identifications are proved; of the minimal set, 96 of 168.
- **Fourth (index 3) is one line from closed**, but blocked by a name clash; see Blockers.
- When the nine coverages close, T4 is a one-line application. A draft `Milestones.lean` patch
  is in the bundle (`tmp/flm-cc-integ/patches/Milestones.patch`).

## Tooling and data bundle (needed to resume)

Everything outside the repo — gate scripts, the identification factory, the ledger, transport
data, worker status files, gate records, and uncommitted draft modules — is in a private Meta
Artifact:

- `meta artifacts.artifact download --id=1119138357373470 --out=/tmp/t4h`
  (UI: https://artifacts.internalmeta.com/a/1119138357373470)
- File `t4-handoff-bundle.tar.zst`, sha256 `859e7d8919ac37892e58eb4ccc19c95ca6fcf2f2075c8189e8ea022d4751d8bd`.
- Extract: `mkdir -p /tmp/t4h/x && tar --zstd -xf /tmp/t4h/t4-handoff-bundle.tar.zst -C /tmp/t4h/x`.
  Then `cp -a /tmp/t4h/x/tmp/. /tmp/`. The scripts use absolute `/tmp/flm-cc-*` paths.
- `x/repo-uncommitted-drafts/FormalizedTextbooks/...` holds 3,377 untracked `.lean` files.
  They had never been compiled, so they are not committed: the lakefile builds every
  `FormalizedTextbooks.*` module.
  - One of them is the Fourth one-liner `GeneratedAxisGlobalTwelveFourthIdentCovered.lean`.
  - Most of the rest are Codex-era Tenth drafts and scratch.

Earlier context:

- Codex-era gap inventory: https://artifacts.internalmeta.com/a/1787305609166607
- Root8 local-count review: https://artifacts.internalmeta.com/a/1974951693421182

### Read first (paths after extraction)

| File | What it is |
|---|---|
| `/tmp/flm-cc-glob-plan.md` | Global coverage design: triality forests, CHEAP/EXPENSIVE bindings, propagation principle (section 2a) |
| `/tmp/flm-cc-gident-split.md`, `/tmp/flm-cc-gident-status.md` | Packed whole-vector identification method (engine) |
| `/tmp/flm-cc-gident2-status.md` | Identification factory, including its usage and "CODEGEN DENSE v2" |
| `/tmp/flm-cc-olean-repair.md` | BUILD RULES at the top; list of heavy (>16 GiB) modules |
| `/tmp/flm-cc-<tag>-status.md` | Per-worker status files (tags listed below). grecip has a `## HANDOFF` section; the others were stopped mid-work by the user, so their last notes are the state |
| `/tmp/flm-cc-ident-ledger.json` | Ledger of the 279 identifications. See the stale-claims note under Blockers |
| `/tmp/flm-cc-ident-index.json` | Cross-family identification index, grouped by triangle, with the minimal set marked |
| `/tmp/flm-cc-*-transporters*.json` | Numeric transport records; `.norm.json` copies use the frozen letter alphabet |
| `/tmp/flm-cc-integ/` | Integration prep: commit-set analysis, build plan, patches, disk report |

## Proof route

1. **Order assembly** (`GeneratedOrderAssembly.lean`, pre-existing):
   `generated_order_of_actual_axis_counts`.
   - Inputs: the global axis orbit count `97239461142009186000` and the feasible orbit count
     `11707448673375`.
   - The pair-stabilizer order `709767191322427392000` is already unconditional.
2. **Global axis count** (worker `glob`, `GeneratedAxisGlobalTwelve*`):
   - Twelve representatives in source Table 1 order: First, Octad, Odd, Fourth, Fifth, Sixth,
     Seventh, Eighth, Ninth, Root8, Twelfth, Tenth. These are catalogue indices 0..11.
   - Exact counts: all closed. The Tenth count is `generatedTenth_actual_local_axis_orbit_card`.
     `generatedAxisGlobalTwelveCounted_closed` is in `...TenthClosedCounts`.
   - Disjointness: proved.
   - `GeneratedAxisGlobalTwelveFamilyCovered i := ∀ h : H, sExtra (rhoLocal h (rep i)) ∈ union`.
     Covering all twelve families gives the whole generated orbit (`..._triality_of_covered`,
     `generatedVectorOrbit_eq_localOrbitUnion`).
   - Final wrapper: `generatedAxisGlobalTwelve_order_of_families` in `...Final`.
3. **Feasible count** (worker `fbridge`, `GeneratedFeasibleAmbient*`):
   - Feasible orbit F ⊆ P0 = {axes orthogonal to the first axis}. This uses form invariance
     under G (`GeneratedForm.lean`).
   - Double counting: |P0 ∩ O_i| · 196560 = |O_i| · s_i.
   - All 12 zero counts s_i are gated:
     - First 93151, Octad 4440, Odd 506, Fourth ≤63, Fifth 16, Sixth 1, Seventh 3, Root8 ≤1;
     - Eighth, Ninth, Twelfth and Tenth are 0.
   - The ten actual class witnesses lie in F, and their sizes sum to 11707448673375. So F = P0
     = the ten-class union. No generation lemma for the full stabilizer is needed.
4. **Feasible classes:** slots 0–5 are Codex-era. The rest are:
   - slots 6–9: `GeneratedFeasible{Fifth,Sixth,Seventh,RootEight}Slot*`, each with
     `..._actual_A_orbit_card`, all independently reviewed and approved;
   - the containing zero fiber: `GeneratedFeasibleContainingZero*`,
     `generatedFeasibleActualTransition_containing_outside_cosets`, forward 4320 / reverse 120.
5. **Coverage of each family** uses three ingredients:
   - a binary *forest*: orbits of the family stabilizer on the 8,292,375 binary Ω classes. Use
     the fast bitset-doubling design, `GeneratedAxisGlobalTwelveTenthForestOps/Linear`;
   - *bindings*: for each forest root and triality sign, the image lies in a catalogue class;
   - *identifications*, which most bindings need: `sExtra^e (rhoLocal h (rep i)) = rhoLocal g
     (rep j)` for explicit local words h, g. These are proved with the packed pairing-128
     criterion; the engine is described below.

   Two reductions cut the work:
   - Reciprocity, plus the propagation principle: one identification binds both sides of a
     cross-family pair.
   - Triangles: σ has order 3, so 2 of the 3 vertices bind a whole triangle.

   **No-cycle rule:** a family's coverage proof may assume `FamilyCovered j` only for j ∈ {0,1,2}.
   Everything else must come from explicit identification lemmas, so that the final assembly is
   acyclic.

## Status per open family

Counts are entries of the minimal identification set touching each family. Shared triangles
count under both families. Claims marked *stale* were held by workers that the user stopped at
wrap-up.

| Idx | Family | Reduction theorem (module) | Minimal: done / stale-claimed / open / failed |
|---|---|---|---|
| 3 | Fourth | `generatedAxisGlobalTwelve_fourth_covered_of_tenth (p5 p8)` (`...FourthIdentAssemblyOdd`). p5 = `tf64p_partner`, p8 = `tf61n_partner`, both gated (`...TenthF64p`, `...TenthF61n`) | 18 / 0 / 0 / 0. **Only the one-liner is left; blocked by the name clash** |
| 4 | Fifth | `generatedAxisGlobalTwelveFifthBind_covered_of_open` (`...FifthBindFinal`, not gated; needs a v2 re-gate together with `...Root13`, `...Reduction`). Remaining: root 7 (both images; F7t± into Eighth[35]), forward images at roots 3 (gforest S7c3+, done), 4 (gninth N7−), 10 (Twelfth F10t±) | 7 / 2 / 0 / 0 |
| 5 | Sixth | `generatedAxisGlobalTwelve_sixth_covered_of_ident` (`...SixthIdent`); triangle and transfer helpers in `...SixthTriangle`, `...SixthTransfer` | 5 / 4 / 0 / 0 |
| 6 | Seventh | `generatedAxisGlobalTwelve_seventh_covered_of_remaining` (`...SeventhIdent`/coverrest). Bound so far: (+) cells 3, 10, 13, 19, 20; (−) cells 1, 3, 18, 20, 22. Later identifications closed (+) 18, 12, 14, (−) 8, 17 (factory). See the gforest status file | 20 / 3 / 1 / 0 |
| 7 | Eighth | `generatedAxisGlobalTwelve_eighth_covered_of (hb : ∀ j ≠ 0, RootBound j)` (`...EighthFamily`), with root wrappers `generatedAxisGlobalTwelveEighthBind_root{j}`. Closed roots: 6, 28 (gident), 9, 26 (factory). Many one-sided roots wait only on partner identifications | 30 / 7 / 15 / 0 |
| 8 | Ninth | `generatedAxisGlobalTwelve_ninth_covered_of_explicit` (`...NinthExplicit`) and `..._RootBound_of_ident_eq` (`...NinthIdent`); 14 equations | 10 / 4 / 0 / 0 |
| 9 | Root8 | `generatedAxisGlobalTwelve_rootEight_covered_of_identifications` (`...RootEightBind`); 22 forward + 15 inverse equations; about 13 closed (r8f status) | 13 / 11 / 2 / 1 |
| 10 | Twelfth | `generatedAxisGlobalTwelve_twelfth_covered_of_ident` (`...TwelfthBind`); root 0 needs no identification (identity pair) | 28 / 6 / 20 / 1 |
| 11 | Tenth | `generatedAxisGlobalTwelve_tenth_covered_closed` (`...TenthClosedFixers`, drops hfix), `..._tenth_covered_of_pure` (`...TenthIdent`), partner lemmas `..._pair_of_partner_forward/inverse`. 12 pure-Tenth identifications plus partner coverage of 51 mixed roots | 34 / 18 / 38 / 0 |

## Identification engine and factory

- **Criterion:** unit axes x = y iff the pairing equals 128 (Cauchy–Schwarz). The pairing is
  split into parts (matrix, pairs, octad, odd, tensor), and each part is its own
  `decide +kernel` theorem.
- **Factory form:** each part is checked against the target's own self-part
  (`GeneratedAxisGlobalIdentWCore`: `self_eq_128`, `ident_forward_self` / `ident_inverse_self`),
  so no predicted values are needed.
- **Packed vectors:** `GeneratedAxisGlobalIdentPacked` holds big-Nat fields.
- **Letter alphabet:** `GeneratedAxisGlobalIdentLetters`, with `IdentLetter = xi | sign a ε | mono l | qel g`.
  - xi has order 3 (`xiSpinLocalFiber_cube`), so xi⁻¹ = xi·xi.
  - The sign inverse rule is in `GeneratedAxisGlobalIdentLettersInv` / `...LettersNorm`.
- **Dense-vector pieces (all gated):**

  | Module | What it gives |
  |---|---|
  | `GeneratedAxisGlobalIdentOddDense` | Dense odd parts in one pass |
  | `...TensorSplit` | Splits tensor fields into high/low halves, so 3 Xi letters fit in w = 64 |
  | `...E8MatZ` / `...MatPairFast` | Fast matrix and pair parts |
  | `...DenseCheck` | Three-segment transport check |
  | `...TensorXiFastRun` / `...TensorXiFast` | Fast long-word tensor action (gtenth) |
  | `GeneratedAxisGlobalTwelveTenthOddChunks` / `...TenthScale` | Odd-part chunking and field scaling |

- **Source vectors**, `<fam>SrcVec*` with `<fam>Src*_rep`:

  | Family | Source vector |
  |---|---|
  | Fifth | `fifthSrcVecW` |
  | Fourth | `fourthSrcVecW` |
  | Sixth | `sixthSrcVecW` / `sixthSXF` |
  | Seventh | `seventhSrcVecW` / `SrcSeventhL` |
  | Eighth | `eighthSrcVecW` / `E8Src*` |
  | Odd | `oddSrcVecW` |
  | Twelfth | `twelfthSrcVecL` |
  | Tenth, Root8, Ninth | `tenthSrcVecL`, `rootEightSrcVecL`, `ninthSrcVecL` |

  Factory glue lives in `GeneratedAxisGlobalIdentWFam*`.
- **Commands:**
  - Run one ledger entry: `python3 /tmp/flm-cc-ident-factory.py run <ledger-id>`.
  - Emit modules only: `/tmp/flm-cc-ident-gen.py <id>`.
  - Claims: `/tmp/flm-cc-ident-claim.py claim|done|fail|release|next`.
  - Cost per identification: 6.5–40 min, peaks of 11–16 GiB, one Lean process.

## Blockers and known issues (fix these first)

1. **Duplicate declarations.** These block Fourth and will block the final assembly.
   - `GeneratedAxisGlobalIdent.ShortData.flat_scale` is declared in both
     `GeneratedAxisGlobalIdentWScale` (2 importers) and `GeneratedAxisGlobalTwelveTenthScale`
     (20 importers). Any module importing both fails ("environment already contains").
   - gident also reported clashes between `TenthOddChunks` (`oddWZ_ofList`, `oddLZ_ofList`,
     `octChunkTerms_append`) and the factory helpers.
   - **Consequence for this commit:** the regenerated collection root
     `FormalizedTextbooks/FrenkelLepowskyMeurmanMonster.lean` imports every committed module,
     including both declarations of `flat_scale`. It therefore **does not compile** until the
     duplicates are renamed, so `lake build FormalizedTextbooks` fails at that root. Every
     individual module was compiled and gated on its own.
   - **Do first:** a global duplicate-declaration scan over all new modules. A single Lean file
     importing every top module is a good test. Rename on the side with fewer importers, then
     re-gate the importers.
   - Then gate `GeneratedAxisGlobalTwelveFourthIdentCovered.lean` (in the drafts). Its content
     is `generatedAxisGlobalTwelve_fourth_covered := generatedAxisGlobalTwelve_fourth_covered_of_tenth tf64p_partner tf61n_partner`.
     Gate it with `python3 /tmp/flm-cc-grecip-tools/v2wrap16.py /tmp/flm-cc-grecip-idcov <module>`.
2. **Build rules** (from Lake 4.34.1 behaviour):
   - lake rebuilds any directly built module that lacks `.ilean`/`.c`, with or without `--old`.
   - 32 modules need more than 16 GiB (up to 47 GiB); see `known-capped.json` in
     `/tmp/flm-cc-glob-repair`. A capped `lake build` that reaches one gets killed and
     **deletes its olean**.
   - So never `lake build` such closures. Gate them with v2:
     `python3 /tmp/flm-cc-direct-gate-v2.py STEM MOD...`. It uses lake-exact options, checks
     import currency, fails on any warning, and never runs lake.
   - The standard gate (`/tmp/flm-transition-recovery-gate-scope.py`) is fine only when
     `lake build --no-build <mods>` reports nothing to build.
3. **The standard gate trusts mtimes.** A source edited during a build was audited stale twice
   (gninth `...NinthBindings`, grecip `...FourthIdentF2Checks`; both were kernel-identical on
   re-check). The final fresh build will catch any remaining case.
4. **Stale ledger claims.** About 45 entries are `claimed` by workers the user stopped. Treat
   them as open, but first check whether their final `*_ident` module is already gated. Search
   `/tmp/*frozen-sha256.json` and `GeneratedAxisGlobalIdentW<Tag>.lean`.
   - Some gates were still running at wrap-up. Their outputs are local only and may be missing
     from this commit.
5. **CI cannot build this as it stands.**
   - The heavy modules exceed 16 GB runners, and a cold build takes far more than 6 h.
   - `scripts/mk_all.sh --check` fails with "Argument list too long" at this module count. A
     tested one-line fix is in `/tmp/flm-cc-integ/patches/mk_all-argmax.patch`; it is **not
     applied** to `scripts/mk_all.sh`.
   - The generated root in this commit was regenerated with a patched temporary copy.
   - Options: a large self-hosted runner for the first build, or split the heavy certificates.
     See `/tmp/flm-cc-integ/build-plan.md`.
6. **Disk.** The host was at 93% during the run (btrfs, zstd).

## How to resume

1. Download and extract the bundle (see above). Read the files listed under "Read first".
2. Fix the duplicate declarations (Blocker 1), then gate the Fourth one-liner. That closes
   `FamilyCovered 3`.
3. Reconcile the ledger's stale claims (Blocker 4). Then run the open minimal identifications
   with the factory, following the build rules and the no-cycle rule. Apply each result to its
   family wrapper; the table above gives the reduction theorems.
4. As each `FamilyCovered i` closes unconditionally, pass it to
   `generatedFeasibleAmbientT4_order_of_families`.
5. When all nine are in:
   - apply `/tmp/flm-cc-integ/patches/Milestones.patch`, replacing its `sorry` placeholder with
     the nine theorems;
   - update the README/GAPS/HUMAN_REVIEW T4 sections;
   - run an independent adversarial review (`REVIEWING.md`);
   - run a fresh full build (plan in `build-plan.md`; about 10–12 h on this host), then
     `scripts/check.sh`.

## Worker tags (status files, module prefixes)

| Tag | Scope |
|---|---|
| glob | Catalogue, final wrapper, build repair, integration prep (`GeneratedAxisGlobalTwelve{Catalogue,Counts,Endpoint,Final,...}`) |
| fbridge | Feasible bridge and T4 assembly (`GeneratedFeasibleAmbient*`) |
| gident, gident2 | Identification engine and factory (`GeneratedAxisGlobalIdent*`) |
| grecip | Reciprocity and Fourth (`GeneratedAxisGlobalTwelveReciprocity*`, `...Fourth*`) |
| gfifth | Fifth (`...FifthBind*`) |
| gforest | Sixth and Seventh (`...Sixth*`, `...Seventh*`, `GeneratedAxisGlobalIdentSrc{Odd,Sixth,Seventh,Eighth}*`) |
| goctad | Octad (closed), Eighth bindings, Tenth/Root8/Ninth sources (`...Octad*`, `...EighthBind*`, `...Src{Tenth,RootEight,Ninth}*`) |
| gninth | Ninth, plus the Eighth forest (`...Ninth*`, `...Eighth{Forest,Family,...}`) |
| r8f | Root8 coverage, slot 9, the index and normalization, the sign fix (`...RootEight*`, `GeneratedFeasibleRootEightSlot*`) |
| gtwelfth | Twelfth (`...Twelfth*`) |
| gtenth | Tenth coverage (`...Tenth*` forest, ident, partners) |
| tenth | Tenth local count (`GeneratedAxisClassificationTenthCC*`) |
| zero | Containing zero fiber (`GeneratedFeasibleContainingZero*`) |
| s6f, s7f, f5f, r8f | Feasible slots 7, 8, 6, 9 |

## Verification facts for this commit

- Every committed new `.lean` module was checked in one of three ways:
  - gated, with the frozen source hash matching (9,400 modules);
  - built, with an olean newer than its source (389);
  - in T4's import closure, which the v2 currency checker reported current at wrap-up: 20,400
    modules (11,492 in the repo), 0 issues.
- Every committed module's in-repo imports are tracked or committed.
- No committed new module contains `sorry`, `native_decide` or `axiom`. The only `sorry`s
  remain T4 and T6 in `Milestones.lean`.
- The gate records (`/tmp/*frozen-sha256.json`, about 6,300) are in the bundle.
