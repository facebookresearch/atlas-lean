# Markov-type properties are undecidable in Burnside varieties of large odd composite exponent

For every large enough odd composite exponent $n$, the analogue of the Adian–Rabin theorem holds in the variety of groups of exponent $n$: no property with a positive witness and a negative witness that persists to overgroups is decidable from finite presentations relative to that variety.

Let $\mathfrak{B}_n$ be the Burnside variety of all groups of exponent $n$ (groups in which $g^n = 1$ for every $g$). A group in $\mathfrak{B}_n$ is finitely presented relative to $\mathfrak{B}_n$ if it is the quotient of a finitely generated free Burnside group $\mathbf{B}(S, n) = F(S) / F(S)^n$ by the normal closure of a finite subset; a finite presentation $\langle S \mid R \rangle$ relative to $\mathfrak{B}_n$ defines the group $\langle S \mid R \rangle / \langle S \mid R \rangle^n$.

There is a critical exponent $n_0$ such that the following holds for every odd integer $n > n_0$ that is not prime. Let $\mathcal{P}$ be a subclass of $\mathfrak{B}_n$ for which there are groups $G_+, G_- \in \mathfrak{B}_n$, finitely presented relative to $\mathfrak{B}_n$, such that

1. $G_+$ belongs to $\mathcal{P}$, and
2. no group of exponent $n$ containing $G_-$ as a subgroup belongs to $\mathcal{P}$.

Then no algorithm takes as input a finite presentation relative to $\mathfrak{B}_n$ and decides whether the group it defines belongs to $\mathcal{P}$ (Theorem 2.9 of the source, stated in the introduction as Theorem 1.2). In particular, for such $n$, being trivial, finite, cyclic, abelian, nilpotent, solvable or amenable is undecidable from finite presentations relative to $\mathfrak{B}_n$ (Corollary 2.10, stated in the introduction as Corollary 1.3).

## Depends on

- [Groups finitely presented in a Burnside variety](../higman-embedding-in-burnside-varieties/burnside-presented.md)
- [Group](../../group-basics/group.md)
- [Abelian group](../../group-basics/abelian-group.md)
- [Amenable group (Følner condition)](../../geometric-group-theory/amenable-groups/is-amenable.md)
- [Varieties of groups](../../varieties-and-equations/axiomatizable-classes-of-groups/is-variety.md)
- [Free Burnside group](../free-burnside-groups/free-burnside-group.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The proof follows the Adian–Rabin scheme inside $\mathfrak{B}_n$. Kharlampovich proved that for every sufficiently large exponent $n$ that is not prime there is a group $H \in \mathfrak{B}_n$, finitely presented relative to $\mathfrak{B}_n$, with unsolvable word problem. For a word $w$ in the generators of $H$, small cancellation theory over free Burnside groups (the source's periodic quotient theorem for small cancellation quotients of free products) builds, effectively in $w$, a group finitely presented relative to $\mathfrak{B}_n$ that is isomorphic to $G_+$ when $w = 1$ in $H$ and contains $G_-$ otherwise; deciding $\mathcal{P}$ would solve the word problem of $H$. The source writes $n = pq$ with $p \ge 3$ prime and $q$ having an odd divisor larger than $665$.

## Sources

- R. Coulon and D. Gruber, "Small cancellation theory over Burnside groups", Advances in Mathematics 353 (2019), 722–775, https://doi.org/10.1016/j.aim.2019.05.029; arXiv:1705.09651v3 (Theorem 2.9 and Corollary 2.10 in Section 2.3, "Decision problems and Rips' construction", stated in the introduction as Theorem 1.2 and Corollary 1.3, and Theorem 2.8 used in the proof, of arXiv:1705.09651v3).
