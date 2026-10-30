# MathlibExt/Biology

Mathematical biology: population genetics, phylogenetics, statistical genetics, epidemiology,
and population dynamics. The library rules in `MathlibExt/README.md` and `REVIEWING.md` apply;
this file records the modeling conventions that make results in different files compatible.

## Placement

| Content | Location |
|---|---|
| Biological models and their theorems | `MathlibExt/Biology/<Area>/…` (areas below) |
| Generic mathematics they need | Mathlib's taxonomy: `MathlibExt/Probability/…`, … |
| Algorithms with correctness proofs | `CSLibExt/Bioinformatics/…` |
| Established results whose proof is deferred | `WantedExt/Biology/…`, `WantedExt/Probability/…` |
| Tests | the mirror path under `MathlibExtTest/` or `CSLibExtTest/` |

Areas: `PopulationGenetics` (with `Coalescent/` and `Diffusion/`), `Phylogenetics`,
`StatisticalGenetics`, `Epidemiology`, `Dynamics`. Distributions, Markov chains, statistics
and combinatorics that are not specific to biology go under `MathlibExt/Probability/…` or
`MathlibExt/Combinatorics/…`.

Namespaces follow the path: `MathlibExt.Biology.<Area>.<Topic>` for models,
`Cslib.Bioinformatics.<Area>.<Topic>` for algorithms, and Mathlib's own namespaces
(`ProbabilityTheory`, `Nat`, `Matrix`, …) for generic lemmas that could move upstream.

Search pinned Mathlib and `MathlibExt`/`CSLibExt` before adding a definition, and reuse what
exists: a model's generator, transition kernel, or holding-time structure should be defined
once and imported by every file that needs it.

## Units and parameters

- **Population size.** A diploid population has `N` individuals and `M = 2N` gene copies.
  Results about a population of `M` exchangeable gene copies (Wright–Fisher, coalescent
  sampling) are stated in `M`; docstrings say how `M` relates to `N`.
- **Time.** Coalescent and diffusion time is measured in units of `2N = M` generations, so a
  pair of lineages coalesces at rate `1`, `k` lineages at rate `k.choose 2`, and `⌊t M⌋`
  generations correspond to `t` time units.
- **Mutation.** `θ = 4Nu` (diploid), where `u` is the per-generation, per-copy mutation rate;
  mutations fall on each lineage at rate `θ / 2` per time unit.
- **Selection.** `σ = 2Ns` for genic (additive) selection, where `s` is the per-allele
  advantage (genotype fitnesses `1 + 2s`, `1 + s`, `1`). The Wright–Fisher diffusion then has
  drift `σ x (1 - x)` and variance `x (1 - x)`, and Kimura's fixation probability is
  `(1 - e^{-2σx}) / (1 - e^{-2σ})` for `σ ≠ 0` and `x` in the neutral case `σ = 0` (its
  continuous extension); a definition must give the neutral branch explicitly rather than rely
  on Lean's `0 / 0 = 0`. A model of a haploid population (for example the Moran
  model with `N` individuals) states its own scaling in its module docstring.
- **Migration.** `4Nm` for the island model, with `m` the per-generation migration fraction.
- **Substitution models.** Branch lengths are expected substitutions per site (`μ * t`).

## Quantities

- **Population versus sample.** Unless a sample statistic is named, quantities are population
  (expected) quantities: `f2 X Y = 𝔼[(p X - p Y) ^ 2]`, `E π = θ`, … A sample statistic (Tajima's
  `π`, `S`, an estimator) is named as such, and any bias correction is explicit.
- **Site frequency spectrum.** The SFS is unfolded (derived-allele counts `i = 1, …, n - 1`)
  unless a file says otherwise.
- **Ploidy.** Diploid unless stated; a haploid statement says so in its docstring.

## Faithfulness

- No "≈". A statement is an exact finite identity (finite `N`, finite sample) or an explicit
  limit (`Filter.Tendsto` with the scaling written out, e.g. `r = 1 + σ / N`, `i = ⌊x N⌋`).
- Docstrings cite the primary source and state units and conventions.
- Every model `structure` has a non-vacuity witness in its test file: a concrete instance
  showing the hypotheses are satisfiable (for example, holding times realized as coordinates of
  a product of exponential laws).
- A model structure must not assume its conclusion or carry unconstrained data; hypotheses that
  are only needed for some theorems go on those theorems.
- Deferred results go to `WantedExt` as precise `theorem_wanted` statements over real
  definitions, never as `sorry` in `MathlibExt`.
