# Monadic second-order logic with the unbounding quantifier

MSO+U extends monadic second-order logic by the unbounding quantifier $\mathsf U X.\,\varphi(X)$, which says that $\varphi(X)$ holds for finite sets $X$ of arbitrarily large size.

**Definition.** *Monadic second-order logic* (MSO) over a structure has first-order variables $x, y, \ldots$ ranging over elements and set variables $X, Y, \ldots$ ranging over arbitrary (possibly infinite) subsets of the domain, atomic formulas from the structure's relations and $x \in X$, Boolean connectives, and quantifiers $\exists x$, $\forall x$, $\exists X$, $\forall X$. *MSO+U* adds formulas $\mathsf U X.\,\varphi(X)$, where $\varphi$ may have other free variables besides $X$, with the semantics: $\mathsf U X.\,\varphi(X)$ holds iff for every $n \in \mathbb N$ there is a finite set $X$ with at least $n$ elements such that $\varphi(X)$ holds. The *MSO+U theory* of a structure is the set of MSO+U sentences true in it. For the structure $(\mathbb N, \le)$, MSO+U sentences describe properties of infinite words by the usual identification of a word with the structure of its positions and letter predicates.

The variant *WMSO+U*, in which set quantifiers range over finite sets only, is decidable on infinite words (Bojańczyk) and on infinite trees (Bojańczyk and Toruńczyk), whereas plain MSO over $(\mathbb N, \le)$ is decidable by Büchi's theorem.

## Depends on

None.

## Proof depends on

None.

## Expansion

The unbounding quantifier expresses boundedness: for a formula describing finite sets attached to positions (for instance, the blocks between consecutive elements of a set), $\neg\mathsf U X$ says that their sizes are bounded. This is how MSO+U defines properties such as "the gaps of an infinite set are unbounded", which are beyond $\omega$-regular languages.

## Sources

- M. Bojańczyk, P. Parys and S. Toruńczyk, "The MSO+U Theory of (N, <) Is Undecidable", in *33rd Symposium on Theoretical Aspects of Computer Science (STACS 2016)*, Leibniz International Proceedings in Informatics 47, Schloss Dagstuhl–Leibniz-Zentrum für Informatik, 2016, pp. 21:1–21:8, <https://doi.org/10.4230/LIPIcs.STACS.2016.21>; read as arXiv:1502.04578v2, <https://arxiv.org/abs/1502.04578v2>: Section 1 (the unbounding quantifier, MSO+U and WMSO+U).
