# Primitive Dirichlet L-functions have no zero of real part greater than 1/2

For every primitive Dirichlet character $\chi$ and every complex number $s$ with
$\operatorname{Re} s > 1/2$, $L(s, \chi) \ne 0$; for the trivial character modulo $1$, whose
L-function is the Riemann zeta function, the pole $s = 1$ is excluded.

This node is the core of Alpöge's proof, cited below, and is still to be broken down into
statements with published proofs. Read in the Lean source of that proof, the proof of this
statement uses, besides results on Dirichlet L-functions:

- Green's description of the cuspidal irreducible characters of $\mathrm{GL}_n(\mathbb{F}_p)$, $p$
  prime: their degrees and their values on regular semisimple classes;
- identities between theta integrals for unitary dual pairs, used together with Howe duality and
  the Siegel–Weil formula rather than derived from them;
- a partial local Langlands correspondence for $\mathrm{GL}_n$ over $p$-adic fields, constructed
  from cuspidal parameters, with global reciprocity entering one uniqueness statement;
- Galois representations and Galois cohomology, through a bound specific to the claimed proof:
  over specified subfields of cyclotomic fields, a sum over primes $\ell$, weighted by
  $\log \ell$, of the lengths of Tate–Shafarevich groups of Tate twists of
  $\mathbb{Q}_\ell/\mathbb{Z}_\ell$;
- a bound for a covolume, assembled from resolution of singularities and principalization in
  characteristic $0$, the Poincaré–Lelong formula, an arithmetic Hilbert–Samuel theorem, Siegel
  toroidal compactifications and further inputs from the geometry of abelian schemes.

A good expansion replaces this page by pages for these inputs and for the steps that combine
them, each with a precise statement and a published source, and keeps the dependence of the
[half-plane form for all characters](grh-dirichlet-half-plane.md) on the primitive case. Steps
specific to that proof get pages once a readable account of them exists.

## Sources

- Proof: L. Alpöge, released 2026-11-20 as a Lean library (<https://alpo.ge/remark.pdf>) proving the Riemann hypothesis and four forms of the generalized Riemann hypothesis for Dirichlet L-functions. The Lean and Mathlib communities certified the statement and the proof of the Riemann hypothesis in a joint statement of 2026-11-21 endorsed by the Lean FRO and the Mathlib Initiative (<https://leanprover-community.github.io/blog/posts/riemann-hypothesis/>); A. Sutherland's independent checks cover the five main theorems of the library (<https://math.mit.edu/~drew/grh/>). Source mirror: <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>. The library has no licence, so ATLAS has no Lean proof. There the statement is the proposition `ZeroFreeAll`, used through `UpperTheory.Top.imprimitive`; it has no exception at $s = 1$ because Mathlib gives $\zeta(1)$ a finite non-zero value. The inputs listed above are, in the archive, `green_of_regular` with `Published.GreenRegularCharacters`; `ThetaIntegralsAgree` and `LocalMatching` beside Howe duality and Siegel–Weil in `SiegelEisensteinSecondTermHypotheses.lean`; `RecTExists`, constructed in `LocalCentralUnits/RecTExists.lean`; the window bound `VWin` of `CharacterBoxes/ExistsPageN.lean`, derived from `Row0b`; and the covolume bound assembled by `topCovolSlim2_use_alt_alt`.
