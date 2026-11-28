# Form classes and proper ideal classes of an imaginary quadratic order

Let $D$ be an
imaginary quadratic discriminant ($D < 0$, $D \equiv 0, 1 \pmod 4$), let $\sqrt{D} = i\sqrt{|D|}$,
and let $\mathcal{O} \subseteq \mathbb{C}$ be a subring whose underlying set is the order
$\mathbb{Z} + \mathbb{Z}\,\frac{D + \sqrt{D}}{2}$ of discriminant $D$. Write $S_D$ for the set of
integer triples $f = (a, b, c)$, standing for $ax^2 + bxy + cy^2$, with $\gcd(a, b, c) = 1$, $a > 0$
and $b^2 - 4ac = D$ (the primitive positive definite forms of discriminant $D$). Then:

1. for $f = (a, b, c) \in S_D$, every period pair with periods $a$ and
   $\frac{-b + \sqrt{D}}{2}$, whose lattice is
   $\mathfrak{a}_f = \mathbb{Z}a + \mathbb{Z}\,\frac{-b + \sqrt{D}}{2}$, is a proper ideal of
   $\mathcal{O}$: its endomorphism ring is $\mathcal{O}$;
2. there is a bijection from the classes of $S_D$ under proper equivalence (equivalence under
   $\mathrm{SL}_2(\mathbb{Z})$) onto the classes, under homothety, of the period pairs that are
   proper ideals of $\mathcal{O}$, sending the class of $f$ to the class of $\mathfrak{a}_f$;
3. the number of these homothety classes is the Gauss class number $h(D)$, the number of reduced
   primitive positive definite forms of discriminant $D$.

The homothety classes of proper ideals are the classes of proper fractional $\mathcal{O}$-ideals
modulo principal ideals, so (3) is $h(\mathcal{O}) = h(D)$; no lattice is required to lie in
$\mathbb{Q}(\sqrt{D})$, as every proper ideal of $\mathcal{O}$ is homothetic to one that does.

## Sources

- David A. Cox, *Primes of the form* $x^2 + ny^2$, Wiley, New York, 1989, Theorem 7.7, as used by David Cox, John McKay and Peter Stevenhagen, *Principal moduli and class fields*, Bull. London Math. Soc. 36 (2004), 3–12, §2, and by Yuri Bilu, Florian Luca and Amalia Pizarro-Madariaga, *Rational products of singular moduli*, J. Number Theory 158 (2016), 397–410, proof of Proposition 2.5; the proof follows Andrew V. Sutherland, *18.783 Elliptic Curves*, lecture notes, MIT OpenCourseWare, Fall 2025, Lectures 15–17 (Lemmas 15.9 and 15.10, Theorems 17.10 and 17.18), and the deduction is written out here.
