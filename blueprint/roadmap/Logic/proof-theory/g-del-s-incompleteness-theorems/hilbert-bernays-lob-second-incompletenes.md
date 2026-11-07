# Gödel's second incompleteness theorem, abstract Hilbert–Bernays–Löb form

Let $\mathcal{L}$
be a set of sentences with an implication $\to$, a sentence $\bot$, a negation satisfying
$\neg A = (A \to \bot)$ for all $A$, and a provability operator
$\Box : \mathcal{L} \to \mathcal{L}$.
Let $U \vdash A$ be a relation between theories $U \subseteq \mathcal{L}$ and sentences
$A \in \mathcal{L}$ such that for every theory $U$ and all sentences $A$, $B$, $C$:
$U \vdash A \to (B \to A)$, $U \vdash (A \to (B \to C)) \to ((A \to B) \to (A \to C))$, and if
$U \vdash A \to B$ and $U \vdash A$, then $U \vdash B$. Let $T_0$ and $T$ be theories such that
$T_0 \vdash A$ implies $T \vdash A$ for every $A$, and suppose there is a sentence $G$ with
$T_0 \vdash G \to \neg \Box G$ and $T_0 \vdash \neg \Box G \to G$. Suppose that for all sentences
$A$, $B$: if $T \vdash A$, then $T \vdash \Box A$; $T \vdash \Box(A \to B) \to (\Box A \to \Box B)$;
and $T \vdash \Box A \to \Box \Box A$. Let $\mathrm{Con} = \neg \Box \bot$. If $T \nvdash \bot$,
then $T \nvdash \mathrm{Con}$.

The derivability conditions and the fixed point are assumed rather than derived from a concrete
encoding of first-order arithmetic.

Proof: Derive the needed implicational combinators from K and S, apply D1–D3 to the Gödel
fixed point $G$, and contrapose $\Box G \to \Box \bot$. This is the Hilbert–Bernays–Löb route
of Hilbert–Bernays (1939) and Löb (1955), as presented by Boolos, Ch. 3, and Smith, Ch. 33.

## Sources

- Kurt Gödel, *Über formal unentscheidbare Sätze der Principia Mathematica und verwandter Systeme I*, Monatshefte für Mathematik und Physik 38 (1931), 173–198; Martin H. Löb, *Solution of a problem of Leon Henkin*, Journal of Symbolic Logic 20 (1955), 115–118.
