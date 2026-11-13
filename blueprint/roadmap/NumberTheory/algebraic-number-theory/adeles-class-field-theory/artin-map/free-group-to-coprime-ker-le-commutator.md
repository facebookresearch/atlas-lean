# The kernel of the free-group map lies in the commutator subgroup

Let $\mathfrak m$ be
a modulus of a number field $K$, let $P$ be the set of nonzero prime ideals of the ring of
integers $\mathcal O_K$ that do not divide the finite part of $\mathfrak m$, and let
$I_K^{\mathfrak m}$ be the group of invertible fractional ideals of $K$ coprime to the finite
part of $\mathfrak m$. The kernel of the homomorphism $F(P) \to I_K^{\mathfrak m}$ from the free
group on $P$ sending each generator $\mathfrak p$ to $\mathfrak p$ is contained in the
commutator subgroup $[F(P), F(P)]$.

## Sources

- direct native counterpart of ATLAS `freeGroupToCoprime_ker_le_commutator` (source lines 429--487). The prime basis-vector computation at source lines 416--427 is replaced by `FractionalIdeal.factorizationMulEquiv_primeUnitFractionalIdeal`. The proof builds the ATLAS retraction to the abelianization through `FractionalIdeal.factorizationMulEquiv`, `Finsupp.comapDomain.addMonoidHom`, `Finsupp.toFreeAbelianGroup`, and `Abelianization.of`; the retraction itself stays private to this proof.
