# Tarski's undefinability theorem

Let $\mathfrak N$ be the standard model of arithmetic, with domain $\mathbb N$ and the standard interpretation of the language of arithmetic, and fix a Gödel numbering $\varphi \mapsto {}^{\#}\varphi^{\#}$ of sentences. A relation $R \subseteq \mathbb N^k$ is *definable in* $\mathfrak N$ if some formula $\theta(x_1, \dots, x_k)$ satisfies $R(n_1, \dots, n_k) \iff \mathfrak N \models \theta(\overline{n_1}, \dots, \overline{n_k})$ for all $n_1, \dots, n_k$. The set $\{{}^{\#}\varphi^{\#} : \mathfrak N \models \varphi\}$ of Gödel numbers of true sentences is not definable in $\mathfrak N$. Every computable relation, and also the halting relation, is definable in $\mathfrak N$; so truth in $\mathfrak N$ is not computable.

## Expansion

This page becomes ready once these prerequisites are stated:

- Arithmetization of syntax and the diagonal lemma (proof prerequisite; stated in another open change)

## Sources

- The Open Logic Project, *The Open Logic Text*, complete build, release 2e19d09 (2026), Section 37.9, Definition 37.11, Lemmas 37.12 and 37.13 and Theorem 37.14, <https://builds.openlogicproject.org/open-logic-complete.pdf>
- A. Tarski, "Der Wahrheitsbegriff in den formalisierten Sprachen", *Studia Philosophica* 1:261–405, 1936
