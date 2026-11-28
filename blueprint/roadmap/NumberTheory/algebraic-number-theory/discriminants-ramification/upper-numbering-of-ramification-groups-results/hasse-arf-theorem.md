# Hasse–Arf theorem

Let $L/K$ be a finite Galois extension of complete discretely valued fields whose residue fields are perfect
of characteristic $p > 0$, whose group $G$ is **abelian**, with ramification groups $G_i$ in the lower numbering
and $G^v$ in the [upper numbering](../ramification-groups-in-the-upper-numbering.md). A real number $v$ is a
**jump** of the filtration $(G^v)$ if $G^{v + \varepsilon} \neq G^v$ for every $\varepsilon > 0$. The
**Hasse–Arf theorem** says that every jump of $(G^v)$ is an integer. In terms of the lower numbering and
Herbrand's function $\varphi_{L/K}$ of [Herbrand's functions](herbrand-functions.md): if $i$ is an integer with
$G_i \neq G_{i+1}$, then $\varphi_{L/K}(i)$ is an integer.

Serre states the theorem for a complete discretely valued field $K$ and a finite abelian extension with
separable residue extension. Without the hypothesis that $G$ is abelian, a jump need not be an integer; Serre
refers for this to his Exercise 2, on a totally ramified extension with the quaternion group of order $8$ as its
group.

## Expansion

This node is still to be broken down. A good expansion states and links:

1. the reduction to Serre's Proposition 11, Chapter V, §7, p. 94: for a cyclic, totally ramified extension, with
   $\mu$ the largest integer such that $G_\mu \neq \{1\}$, the number $\varphi_{L/K}(\mu)$ is an integer. The
   reduction replaces $G$ by its inertia group, puts $G' = G^v$ and $G'' = G^{v + \varepsilon}$ for small
   $\varepsilon > 0$, chooses a cyclic quotient $H$ of $G/G''$ in which the image $H'$ of $G'$ is nontrivial, and
   applies [Herbrand's theorem](herbrand-s-theorem.md) in the form $H^v = H'$, $H^{v + \varepsilon} = \{1\}$ of the
   compatibility of the upper numbering with quotients (p. 94); Exercise 3 of Chapter IV, §3, p. 77, asks to
   show that the theorem for cyclic groups of prime power order implies it in general;
2. the proof of Proposition 11, pp. 94–96, after an extension of the residue field making it not the prime
   field (Chapter V, §4, cited on p. 94): with $s$ a generator of $G$, $V$ the elements of norm $1$ of $L^\times$
   and $W$ the subgroup of the $y^{s-1}$ with $y$ a unit, the group $V/W$ is cyclic, by Hilbert's Theorem 90 in
   the form that $V$ is the set of all $y^{s-1}$, $y \in L^\times$ (Lemma 8, citing Bourbaki, *Algèbre*,
   Chapter V, §11, Theorem 3; not read here); then Lemmas 9–13 on the filtrations $V_m = V \cap U_L^m$ and
   $W_m = W \cap U_L^m$, which use Proposition 8 and Corollary 3 to Proposition 9 of Chapter V on the norm on
   the groups of units (cited on p. 96; Lemmas 10–12, on p. 95, not read here), and the final valuation
   argument on p. 96.

## Depends on

- [Upper numbering of ramification groups](../ramification-groups-in-the-upper-numbering.md), for the filtration $(G^v)$
- [Herbrand's functions](herbrand-functions.md), for $\varphi_{L/K}$ and the groups $G_i$, in the second form

## Proof depends on

- [Herbrand's theorem](herbrand-s-theorem.md), for the reduction to cyclic quotients (expansion item 1)
- [Upper numbering of ramification groups](../ramification-groups-in-the-upper-numbering.md), for the compatibility $(G/H)^v = G^v H/H$ of the upper numbering with quotients and $G^{\varphi_{L/K}(u)} = G_u$, which translates the first form into the second
- [Hilbert's Theorem 90 for the multiplicative group](../../../../FieldTheory/galois-theory/multiplicative-hilbert-s-theorem-90.md), in the cyclic form used by Serre's Lemma 8: the elements of norm $1$ are the $y^{s-1}$, $y \in L^\times$ (expansion item 2)

## Sources

- J.-P. Serre, *Local Fields*, Graduate Texts in Mathematics 67, Springer, 1979:
  - Chapter IV, §3, p. 75, Remark 1 ("One says that $v$ is a "jump" for the filtration if $G^v \neq G^{v + \varepsilon}$
    for all $\varepsilon > 0$. Even when $L/K$ is finite, a jump need not be an integer (cf. exer. 2).");
  - Chapter IV, §3, p. 76: Theorem (Hasse–Arf), "If $G$ is an abelian group, and if $v$ is a jump in the
    filtration $G^v$, then $v$ is an integer. [In other words, if $G_i \neq G_{i+1}$, then $\varphi(i)$ is an
    integer.] A proof will be given in §7, Chap. V.", with the Remark that Hasse proved it for a finite residue
    field and Arf in general, and the Example of cyclic groups of order $p^n$;
  - Chapter IV, §3, Exercises 2 and 3, p. 77;
  - Chapter V, §7, "Application: Proof of the Hasse–Arf Theorem", pp. 93–96: Theorem 1, p. 93, Theorem 1′ and
    Proposition 11, p. 94, the reduction of Theorem 1 to Proposition 11, p. 94, Lemmas 8 and 9, p. 94, and
    Lemma 13 and the proof of Proposition 11, p. 96.
