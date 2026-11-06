---
not_ready: true
---

# 3. Identifying the Monster

Establish the global claims for the concrete group $G$. Keep its provisional
name until the construction and identification have been checked against FLM.

## Four distinct obligations

1. **Finiteness:** prove $G$ is finite using the source argument. A finite
   generating set and a finite-dimensional representation do not suffice.
2. **Order:** prove

   $$
   |G|=2^{46}3^{20}5^9 7^6 11^2 13^3
   17\,19\,23\,29\,31\,41\,47\,59\,71.
   $$

   Trace the source's structural counting argument and its actual orbit,
   stabilizer, index, or centralizer inputs. The displayed value is the agreed
   project target, not a source-verified passage in this PR.
3. **Simplicity:** prove nontriviality and that every normal subgroup is either
   the identity subgroup or $G$. Trace each specialized finite-group input;
   do not put simplicity into the definition of $G$.
4. **Identification:** verify correspondence with the classical FLM construction,
   including its definitions and proof inputs. If an independent model or
   recognition theorem is used, prove the required comparison or theorem.
   Simplicity and the displayed order alone do not supply this identification.

## Proof boundary

Adopt a constructive FLM model instead of an unverified abstract group named
Monster. The source audit must determine whether FLM identifies a concrete
model directly or uses additional recognition results. Record the actual route
before expanding the fine theorem DAG.

External computations may generate data or certificates, but Lean must check
them. An ATLAS entry, GAP computation, or unchecked representation is not proof
evidence. Finished results follow the repository's axiom policy and prohibition
on native_decide.

The eventual VOA embedding uses this substantiated model and the separate
generator lifts. Defining the Monster as the full VOA automorphism group would
not discharge these finite-group obligations.

## Completion criterion

All four obligations and their transitive prerequisites must have checked
proofs, with the source comparison documented. Results assuming unproved local
structure, Conway-group facts, or recognition hypotheses remain conditional.

## Source questions

- Locate the separate finiteness, order, and simplicity arguments.
- List the earlier subgroup and involution-centralizer facts they use.
- Follow every cited finite-group reference and obtain its proof.
- Determine whether identification needs a comparison, classification, or
  recognition theorem, and include that theorem if used.

Full automorphism equality, representation irreducibility, character formulas,
and genus-zero moonshine are later projects, not corollaries asserted here.

## Depends on

- [The extra FLM symmetry](../extra-symmetry/README.md)

## Sources

- [FLM passage checklist](../../sources/flm.md)
- [Project-authored scope](../../sources/scope.md)
