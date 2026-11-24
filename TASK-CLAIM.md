# Task claim: uniqueness for the one-dimensional Dirichlet problem

This temporary note opens the draft pull request that claims the ATLAS task
`af_f688a8daa08a454871a4f99f`. It will be removed when the proof lands on this branch.

- Article: `blueprint/roadmap/Analysis/ordinary-differential-equations/sturm-liouville-dirichlet-problem/dirichlet-1d-unique.md`
- Lean declaration: `MathlibExt.Analysis.Distribution.Dirichlet1DWanted.dirichlet_1d_unique`, the only
  declaration of `WantedExt/Analysis/Distribution/Dirichlet1DWanted.lean`
- Sources: Mathlib `docs/undergrad.yaml` (the one-dimensional Dirichlet problem); L. Evans,
  *Partial Differential Equations*, Ch. 6.

Statement to prove, with its name and statement unchanged: if $u_1, u_2 : \mathbb{R} \to \mathbb{R}$
are twice continuously differentiable, vanish at $0$ and $1$, and satisfy $u_i'' = f$ on $(0, 1)$,
then $u_1 = u_2$ on $[0, 1]$.
