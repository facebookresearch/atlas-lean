# Canonical collections for the integers

A canonical collection for $\mathbb Z$ is the digit-set collection of a mixed-radix number system whose digits at each place form a complete residue system containing $0$; it is complete when it is an additive system for the integers.

Let $(b_i)_{i\ge0}$ be integers with $b_i>1$, and for each $i$ let $T_i\subseteq\mathbb Z$ be a complete residue system modulo $b_i$ containing $0$, that is, a set containing exactly one integer [congruent](../../../GroupTheory/group-basics/congruence-modulo.md) to each integer modulo $b_i$. The *canonical collection* defined by $(b_i)$ and $(T_i)$ is

$$
\{T_0,\ b_0T_1,\ b_0b_1T_2,\ b_0b_1b_2T_3,\ \dots\},
$$

where $cT=\{ct : t\in T\}$. Its sumset is always direct, and it is *complete* if it is an [additive system](additive-systems-for-a-commutative-monoid.md) for $\mathbb Z$. Writing $t_i(n)$ for the element of $T_i$ congruent to $n$ modulo $b_i$, the *canonical system* of the data $(b_i)$, $(T_i)$ (Definition 5; it depends on this ordered presentation, not only on the collection, by Fact 5 and Non-example 1) is the sequence of maps $f_i(n)=(n-t_i(n))/b_i$ on $\mathbb Z$, and the *trajectory* of $n$ is $n,\ f_0(n),\ f_1(f_0(n)),\ \dots$.

For $T_i=\{0,1,\dots,b_i-1\}$ the collection is a mixed-radix number system for $\mathbb N_0$, and its sumset is $\mathbb N_0$, not $\mathbb Z$; the choices $T_i=\{0,(-1)^i\}$ with $b_i=2$ (negabinary), and $T_i=\{-1,0,1\}$ with $b_i=3$ (balanced ternary), give complete canonical collections. An integer $n$ lies in the sumset of a canonical collection iff its trajectory is eventually $0$ (Proposition 1 of the source), so the collection is complete iff every trajectory is eventually $0$ (Corollary 1).

## Depends on

- [Additive systems for a commutative monoid](additive-systems-for-a-commutative-monoid.md)
- [Congruence modulo an element of an additive commutative monoid](../../../GroupTheory/group-basics/congruence-modulo.md)

## Proof depends on

None.

## Expansion

Directness: if $n=a_0+a_1+\cdots$ with $a_i\in b_0\cdots b_{i-1}T_i$, then $a_0$ is the unique element of $T_0$ congruent to $n$ modulo $b_0$, and inductively $a_i$ is determined by $n-(a_0+\cdots+a_{i-1})$ modulo $b_0\cdots b_i$. The digits produced this way are $b_0\cdots b_{i-1}\,t_i(n_i)$ with $n_i$ the $i$th term of the trajectory of $n$, and the representation is finite exactly when the trajectory reaches $0$, after which it stays at $0$.

## Sources

- Andrei Zabolotskii, "Additive systems for $\mathbb Z$ are undecidable", *Journal of Combinatorial Mathematics and Combinatorial Computing* 130:241–253, 2026, doi:[10.61091/jcmcc130-16](https://doi.org/10.61091/jcmcc130-16); read in arXiv:2508.17285v2, whose numbering is used here: Examples 4 and 5 (negabinary and balanced ternary), Definition 4 with the facts after it (Fact 1, directness; Fact 5 and Non-example 1, the dependence on the ordering), Equation (2) and Definition 5 in Section 4, Proposition 1 and Corollary 1.
