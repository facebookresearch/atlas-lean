# Probabilistic higher-order recursion schemes

A probabilistic higher-order recursion scheme is a finite set of simply typed rewrite rules, one per non-terminal, each choosing between two right-hand sides with a fixed rational probability. Its termination probability is the probability that rewriting from the start symbol reaches the terminating constant.

**Types and terms.** Types are $\kappa ::= \mathtt{o} \mid \kappa_1 \to \kappa_2$, with order $\mathrm{order}(\mathtt{o}) = 0$ and $\mathrm{order}(\kappa_1 \to \kappa_2) = \max(\mathrm{order}(\kappa_1) + 1, \mathrm{order}(\kappa_2))$. Applicative terms are $t ::= \mathtt{e} \mid \Omega \mid x \mid t_1\, t_2$, where the constants $\mathtt{e}$ (termination) and $\Omega$ (divergence) have type $\mathtt{o}$ and terms are typed by the usual simple type system.

**Definition (Kobayashi, Dal Lago and Grellois).** A *probabilistic higher-order recursion scheme* (pHORS) is a triple $\mathcal{G} = (\mathcal{N}, \mathcal{R}, S)$ where

1. $\mathcal{N}$ maps a finite set of non-terminals to types;
2. $\mathcal{R}$ assigns to each non-terminal $F$ with $\mathcal{N}(F) = \kappa_1 \to \cdots \to \kappa_k \to \mathtt{o}$ a rule $F\, x_1 \cdots x_k = t_L \oplus_p t_R$, with $p \in [0,1]$ rational and $t_L, t_R$ applicative terms of type $\mathtt{o}$ under $\mathcal{N}, x_1 : \kappa_1, \dots, x_k : \kappa_k$;
3. $S$ is a non-terminal with $\mathcal{N}(S) = \mathtt{o}$, the start symbol.

The *order* of $\mathcal{G}$ is the largest order of the types of its non-terminals.

**Semantics.** If $\mathcal{R}(F) = \lambda x_1 \cdots x_k.\, t_L \oplus_p t_R$, then $F\, t_1 \cdots t_k$ rewrites to $[t_1/x_1, \dots, t_k/x_k]\, t_L$ with probability $p$ and to $[t_1/x_1, \dots, t_k/x_k]\, t_R$ with probability $1 - p$; rewriting acts on the head of the term. For a word $\pi \in \{L, R\}^\ast$ of choices let $\mathcal{P}(\mathcal{G}, \pi)$ be the product of the probabilities along the rewriting sequence from $S$ that follows $\pi$ if that sequence ends in $\mathtt{e}$, and $0$ otherwise. The *termination probability* is

$$
\mathcal{P}(\mathcal{G}) = \sum_{\pi \in \{L,R\}^\ast} \mathcal{P}(\mathcal{G}, \pi) \in [0, 1].
$$

$\mathcal{G}$ is *almost surely terminating* if $\mathcal{P}(\mathcal{G}) = 1$.

## Depends on

- [Simple types](../../../type-systems-and-lambda-calculi/simply-typed-lambda-calculus/ty.md)

## Proof depends on

None.

## Expansion

Order-1 schemes have essentially the expressive power of probabilistic pushdown systems and recursive Markov chains, whose termination probabilities are least solutions of polynomial fixpoint equations over the reals. At order $2$ and above non-terminals take functions as arguments, and almost-sure termination becomes undecidable.

## Sources

- Naoki Kobayashi, Ugo Dal Lago and Charles Grellois, "On the Termination Problem for Probabilistic Higher-Order Recursive Programs", Logical Methods in Computer Science 16(4), Article 2, 2020, <https://doi.org/10.23638/LMCS-16(4:2)2020>; Definitions 2.1 and 2.2 in Section 2 of arXiv:1811.02133v5, <https://arxiv.org/abs/1811.02133v5>.
