# Theorem of the cube, theorem of the square and the seesaw principle

This node is still to be broken down. It covers the first results on line bundles on an
[abelian variety](abelian-scheme.md) $A$ over a field $k$, those that come before
[projectivity](abelian-varieties-are-projective.md) and the construction of the
[dual abelian variety](dual-abelian-variety.md). The targets are:

1. (Seesaw principle.) Let $X$ be a complete variety and $Y$ a variety over $k$, and $L$, $M$ line
   bundles on $X \times Y$ with $L|_{X \times \{y\}} \cong M|_{X \times \{y\}}$ for all closed points
   $y$. Then $L \cong M \otimes \mathrm{pr}_Y^* N$ for a line bundle $N$ on $Y$, and $L \cong M$ if
   moreover $L|_{\{x\} \times Y} \cong M|_{\{x\} \times Y}$ for some point $x$. The proof uses that
   $H^0(X, \mathcal{O}_X) = k$; for a complete $X$ with several connected components the pull-backs on
   different components need not come from one line bundle on $Y$.
2. (Triviality locus.) For $X$ complete and $L$ a line bundle on $X \times Y$, the set of $y$ with
   $L|_{X \times \{y\}}$ trivial is closed, and is the support of a maximal closed subscheme
   $Y_0 \subset Y$ over which $L$ is a pull-back from $Y_0$.
3. (Theorem of the cube.) If $X$, $Y$ are complete varieties, $Z$ is a connected locally noetherian
   scheme, $x \in X(k)$, $y \in Y(k)$, $z \in Z$, and $L$ is a line bundle on $X \times Y \times Z$
   whose restrictions to $\{x\} \times Y \times Z$, $X \times \{y\} \times Z$ and $X \times Y \times
   \{z\}$ are trivial, then $L$ is trivial. For a line bundle $L$ on $A$, the line bundle
   $\Theta(L) = \bigotimes_{I \subset \{1, 2, 3\}} p_I^* L^{(-1)^{1 + \# I}}$ on $A^3$, with
   $p_I$ the partial sums, is trivial.
4. (Consequences.) $n_A^* L \cong L^{(n^2 + n)/2} \otimes (-1)_A^* L^{(n^2 - n)/2}$ for every integer
   $n$; and the theorem of the square: $t_{x+y}^* L \otimes L \cong t_x^* L \otimes t_y^* L$ for
   $x, y \in A(k)$, and more generally, for a $k$-scheme $T$ and $x, y \in A(T)$, the same identity on
   $A_T$ up to the pull-back of a line bundle on $T$. Hence $x \mapsto t_x^* L \otimes L^{-1}$ is a
   homomorphism $A(k) \to \operatorname{Pic}(A)$.
5. (The group $K(L)$.) The closed subgroup scheme $K(L) \subset A$, the maximal closed subscheme over
   which the Mumford bundle $\Lambda(L) = m^* L \otimes \mathrm{pr}_1^* L^{-1} \otimes \mathrm{pr}_2^*
   L^{-1}$ on $A \times A$ is a pull-back from the second factor, and its finiteness for ample $L$.

A good expansion follows van der Geer and Moonen, Chapter II, whose proof of the theorem of the cube
uses the triviality locus and Krull's intersection theorem; Milne's notes state the same results
(Theorem I.5.1 and its corollaries, Theorems I.5.5 and I.5.16), but the version 2.00 of his notes leaves
the last step of the proof of the theorem of the cube to a later version, referring to Mumford's
*Abelian Varieties*, pp. 57–58.

## Depends on

- [Abelian scheme](abelian-scheme.md), for abelian varieties over a field

## Sources

- G. van der Geer and B. Moonen, *Abelian Varieties*, book draft, Chapter II, "Line bundles and
  divisors on abelian varieties", <https://www.math.ru.nl/personal/bmoonen/BookAV/LineBund.pdf>:
  Theorem (2.1) and the See-saw Principle (2.2), Lemmas (2.3) and (2.4) (triviality locus, referring
  to Mumford's *Abelian Varieties*, §10, or to Picard schemes), Theorem (2.5) and Remarks (2.6),
  Theorem of the Cube (2.7), Theorem of the Square (2.9) and Corollary (2.10), pp. 16–20; the Mumford
  bundle and $K(L)$, Definitions (2.15)–(2.16), Lemma (2.17), Proposition (2.18) and Lemma (2.19)
  ($K(L)$ is finite for ample $L$), pp. 21–23.
- J. S. Milne, *Abelian Varieties*, course notes, version 2.00 (2008),
  <https://www.jmilne.org/math/CourseNotes/AV.pdf>: Chapter I, §5 (Theorem 5.1, Corollaries 5.2–5.4,
  Theorem 5.5, Remark 5.6, Theorem 5.16, Corollaries 5.17–5.18, Proposition 5.19, and the end of the
  section after Lemma 5.20).
- D. Mumford, *Abelian Varieties*, Tata Institute of Fundamental Research Studies in Mathematics 5,
  Oxford University Press, 1970: §§5–6 and §10, as cited above.
