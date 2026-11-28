# Oesterlé's effective lower bound for class numbers

Let $D < 0$ be a fundamental discriminant and put $d = |D|$. Let $P(d)$ be the set of primes
dividing $d$ other than the largest one, and let

$$\vartheta(d) = \prod_{p \in P(d)} \left(1 - \frac{\lfloor 2\sqrt{p} \rfloor}{p + 1}\right),$$

the empty product being $1$. Then

$$\vartheta(d) \log d \le 7000\, h(D),$$

where $\log$ is the natural logarithm and $h(D)$ is the Gauss class number of $D$, the number of
primitive positive definite reduced binary quadratic forms of discriminant $D$.

For a fundamental discriminant $D$ this $h(D)$ is the class number of the imaginary quadratic field
of discriminant $D$: Oesterlé (§§1.2–1.3) identifies its ideal class group with the proper
equivalence classes of positive definite forms of discriminant $D$, each of which contains exactly
one reduced form, and a form whose discriminant is fundamental is primitive.

Oesterlé's Théorème 1 gives an effectively computable constant $C$ with
$\vartheta(d) \log d \le C\, h(D)$ for every such $D$; his §5.1 states that $C = 7000$ is
admissible, referring the computation to his announced article *Résolution effective du problème du
nombre de classes des corps quadratiques imaginaires*. The proof applies Goldfeld's theorem to a
modular form that Gross and Zagier showed to have an $L$-function vanishing to order at least $3$
at $s = 1$.

## Expansion

A good expansion has pages for Goldfeld's theorem, which turns a suitable modular form whose
$L$-function vanishes to order at least $3$ at $s = 1$ into an effective lower bound for $h(D)$ in
terms of $\vartheta(|D|) \log |D|$ (Goldfeld 1976; Oesterlé §3 gives a simplified proof); for the Gross–Zagier theorem (Theorem 8.1) and the modular form it
provides, whose $L$-function vanishes to order at least $3$ at $s = 1$ (Oesterlé §4); and for the
computation of the admissible constant $C = 7000$, which §5.1 defers to Oesterlé's announced
article. Each page states its result precisely, with the locators below.

## Depends on

- [Gauss class number of a discriminant](kronecker-s-class-number-sums/gauss-class-number.md)
- [Fundamental imaginary quadratic discriminant](../../algebraic-number-theory/quadratic-fields/imaginary-quadratic-discriminants/is-fundamental-imaginary-quadratic-discr.md)

## Sources

- Joseph Oesterlé, *Nombres de classes des corps quadratiques imaginaires*, Séminaire Bourbaki, vol. 1983/84, exposé 631, Astérisque 121–122 (1985), 309–323, Théorème 1 (p. 310), §§1.2–1.3 (p. 311–312) and §5.1 (p. 321), [https://www.numdam.org/item/SB_1983-1984__26__309_0/](https://www.numdam.org/item/SB_1983-1984__26__309_0/).
- Guy Fowler, *Some uniform effective results on André–Oort for sums of powers in* $\mathbb{C}^n$, Math. Proc. Cambridge Philos. Soc. 180 (2026), 607–641, [proof of Proposition 2.6, p. 615](https://doi.org/10.1017/S0305004125101825), which quotes the bound in this form.
- D. Goldfeld, *The class number of quadratic fields and the conjectures of Birch and Swinnerton-Dyer*, Ann. Scuola Norm. Sup. Pisa Cl. Sci. (4) 3 (1976), 624–663.
- B. Gross and D. Zagier, *Heegner points and derivatives of L-series*, Invent. Math. 84 (1986), 225–320, Theorem 8.1.
