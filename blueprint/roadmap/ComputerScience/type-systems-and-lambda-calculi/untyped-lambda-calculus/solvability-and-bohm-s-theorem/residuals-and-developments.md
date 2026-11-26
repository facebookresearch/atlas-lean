# Residuals and developments

Let $t$ be an untyped λ-term and $R$ a set of β-redex occurrences of $t$. Mark the redexes of $R$, for example by underlining their λ; terms with
marks form the *marked λ-calculus*, in which only marked redexes may be contracted.

- **Residuals.** If $t'$ is obtained by contracting one redex $r_0$ of $t$, in $R$ or not, the *residuals* of $R$ in $t'$ relative to $r_0$ are found by marking the redexes
  of $R \cup \{r_0\}$, contracting the marked $r_0$, and taking the redexes of $t'$ that still carry a mark (substitution copies, moves or erases marked redexes, and
  the contracted redex itself leaves no residual). Residuals relative to a reduction sequence $r_0, \dots, r_{n-1}$ are defined by iterating this.
- **Developments.** A *development* of $(t, R)$ is a reduction sequence $t = t_0, t_1, \dots, t_n$ in which $r_0 \in R$ and each contracted redex $r_i$ is a
  residual of $R$ relative to $r_0, \dots, r_{i-1}$; it is *complete* if $R$ has no residual in $t_n$.

The set of residuals depends on the contracted redex and not only on $t$ and $t'$: with $t = (\lambda x.\, x)\, ((\lambda x.\, x)\, x)$, contracting $t$ itself or its
inner redex $(\lambda x.\, x)\, x$ both give $(\lambda x.\, x)\, x$, but $\{t\}$ has a residual only in the second case.

## Depends on

- [Named, de Bruijn and locally nameless lambda terms](../../syntax-with-binders/named-de-bruijn-and-locally-nameless-lambda-terms.md)

## Sources

- J.-L. Krivine, *Lambda-Calculus, Types and Models*, translated from the French by R. Cori, revised online edition, 2011, <https://www.irif.fr/~krivine/articles/Lambda.pdf>: Chapter 4, Section 2 (the calculus $\Lambda(c)$ of representatives, Lemma 4.37, the definitions of residues, developments and complete developments, and the example after them).
