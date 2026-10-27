---
article_id: af_9ccd6a554e1f52f12735b95b
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Analysis.Complex.RiemannMappingWanted.riemannMapping_normalized
---

# Riemann Mapping

For open simply connected proper `U ⊆ ℂ` and `z₀ ∈ U`, there exists holomorphic bijection `f : U →
ball 0 1` with `f z₀ = 0` and `deriv f z₀` positive real, unique up to `Set.EqOn` on `U`. Source:
same as Riemann mapping; B. Riemann thesis 1851; W. F. Osgood Trans. Amer. Math. Soc. 1 (1900),
310–314, DOI 10.2307/1986285; C. Carathéodory Math. Ann. 72 (1912), 107–144, DOI
10.1007/BF01456892; Ahlfors; Lean adds f z₀=0 positive real derivative via im=0 re>0 and EqOn
uniqueness on U.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Is Locally Uniformly Bounded On](normal-families/is-locally-uniformly-bounded-on.md)
- [Is Locally Uniformly Bounded On of forall norm le](normal-families/is-locally-uniformly-bounded-on-of-foral.md)
- [Montel](normal-families/montel.md)

## Sources

- [MathlibExt, MathlibExt.Analysis.Complex.RiemannMapping](../../../../../../sources/v2/MathlibExt.md)
