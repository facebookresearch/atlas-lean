# Periodicity and reachability of Reeb orbits are undecidable on every contact three-manifold

Every contact three-manifold carries a defining contact form whose Reeb flow has explicit points for which no algorithm decides whether the orbit is periodic; for Turing complete Reeb flows, whether orbits from an explicit compact set reach an explicit open set is undecidable.

Let $(M, \xi)$ be a contact three-manifold, $\alpha$ a [contact form](../../../Geometry/complex-and-symplectic-geometry/weinstein-conjecture/is-contact-form3.md) with $\ker \alpha = \xi$, and $R$ its [Reeb vector field](../../../Geometry/complex-and-symplectic-geometry/weinstein-conjecture/is-reeb-vector-field.md), determined by $\alpha(R) = 1$ and $\iota_R \, d\alpha = 0$. A vector field $X$ on $M$ is *Turing complete* if for every integer $k \ge 0$, every Turing machine $T$, every input tape $t$ and every finite string $(t^*_{-k}, \ldots, t^*_k)$ of tape symbols, there are an explicitly constructible point $p \in M$ and an open set $U \subset M$ such that the trajectory of $X$ through $p$ meets $U$ if and only if $T$ halts on $t$ with an output tape whose positions $-k, \ldots, k$ carry the symbols $t^*_{-k}, \ldots, t^*_k$.

**Theorem (Cardona–Miranda–Peralta-Salas).**

1. Let $R$ be a Turing complete Reeb flow on $(M, \xi)$. Then there are an explicitly constructible compact set $K \subset M$ and an explicit open set $U \subset M$ such that it is undecidable whether the positive integral curves of $R$ through the points of $K$ meet $U$ (Corollary 3.5 of the source).
2. There is a contact form $\alpha$ defining $\xi$ whose Reeb field $R$ has explicit points on $M$ for which it is undecidable whether the orbit through a given one of these points is periodic (Corollary 3.7).

Turing complete Reeb flows exist on every contact three-manifold (Theorem 3.3 of the source, after earlier work of the same authors), and through the correspondence between Reeb flows and Beltrami fields they yield Turing complete steady Euler flows on a Riemannian three-sphere.

## Depends on

- [Reeb vector fields](../../../Geometry/complex-and-symplectic-geometry/weinstein-conjecture/is-reeb-vector-field.md)
- [Vector fields with a closed orbit](../../../Geometry/complex-and-symplectic-geometry/weinstein-conjecture/has-closed-reeb-orbit.md)
- [Contact condition for a one-form](../../../Geometry/complex-and-symplectic-geometry/weinstein-conjecture/is-contact-form3.md)
- [Integral curves](../../../Geometry/complex-and-symplectic-geometry/weinstein-conjecture/is-integral-curve.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The halting problem for single-tape machines is undecidable](../../../TheoryOfComputation/computability/halting-problem-for-single-tape-turing-machines/exists-not-tm2-decidable-tm0-halts-on.md)

## Expansion

A reversible universal Turing machine is conjugate to a bijective generalized shift (in the sense of Moore), which acts on a square Cantor set in the disk. That action extends to an area-preserving diffeomorphism of the disk that is the identity near the boundary (Proposition 3.2 of the source), and every such diffeomorphism is the first return map of the Reeb flow of some defining contact form, on a Poincaré section (Theorem 3.3). Clause 1 follows because Turing completeness turns the halting problem into a reachability question. For clause 2, the source first builds a universal reversible machine with a "restart" property: when it halts on an input it returns to the initial configuration (Lemma 3.6, formalizing a construction of Kari and Ollinger). Setting its halting transition back to the initial state makes the orbit of the corresponding point periodic exactly when the machine halts. The generalized shift, the disk-map extension, the Reeb realization theorem and the restart lemma have no pages.

## Sources

- R. Cardona, E. Miranda and D. Peralta-Salas, "Looking at Euler flows through a contact mirror: universality and undecidability", in: European Congress of Mathematics (Portorož, 2021), EMS Press, 2023, 367–393, https://doi.org/10.4171/8ecm/31; read in arXiv:2107.09471v1 (Definition 3.1, Proposition 3.2, Theorem 3.3, Corollaries 3.5 and 3.7 and Lemma 3.6 of arXiv:2107.09471v1, numbering checked against the rendered copy).
