# Discounted LTL

Discounted LTL assigns each infinite computation a satisfaction value in $[0,1]$ instead of true or false. It adds to LTL discounting-until operators $\varphi \mathbin{U_\eta} \psi$ whose value decays with the time needed to fulfil the eventuality, according to a discounting function $\eta$, and its extension adds an average operator $\varphi \oplus \psi$.

**Discounting functions.** A function $\eta : \mathbb{N} \to [0,1]$ is a *discounting function* if it is strictly decreasing and $\lim_{i \to \infty} \eta(i) = 0$; examples are $\eta(i) = \lambda^i$ for $\lambda \in (0,1)$ and $\eta(i) = 1/(i+1)$.

**Syntax.** For a set $\mathcal{D}$ of discounting functions, the formulas of $\mathrm{LTL}^{\mathrm{disc}}[\mathcal{D}]$ over a set $AP$ of atomic propositions are

$$
\varphi ::= \mathrm{True} \mid p \mid \neg\varphi \mid \varphi \vee \varphi \mid X\varphi \mid \varphi \mathbin{U} \varphi \mid \varphi \mathbin{U_\eta} \varphi
$$

with $p \in AP$ and $\eta \in \mathcal{D}$. The logic $\mathrm{LTL}^{\mathrm{disc}\oplus}[\mathcal{D}]$ also allows $\varphi \oplus \psi$.

**Semantics.** For a computation $\pi = \pi_0 \pi_1 \cdots \in (2^{AP})^\omega$ with suffixes $\pi^i = \pi_i \pi_{i+1} \cdots$, the value $[\![\pi, \varphi]\!] \in [0,1]$ is defined by $[\![\pi, \mathrm{True}]\!] = 1$; $[\![\pi, p]\!] = 1$ if $p \in \pi_0$ and $0$ otherwise; $[\![\pi, \neg\varphi]\!] = 1 - [\![\pi, \varphi]\!]$; $[\![\pi, \varphi \vee \psi]\!] = \max([\![\pi, \varphi]\!], [\![\pi, \psi]\!])$; $[\![\pi, X\varphi]\!] = [\![\pi^1, \varphi]\!]$;

$$
[\![\pi, \varphi \mathbin{U} \psi]\!] = \sup_{i \geq 0} \min\Big([\![\pi^i, \psi]\!], \min_{0 \leq j < i} [\![\pi^j, \varphi]\!]\Big),
$$

$$
[\![\pi, \varphi \mathbin{U_\eta} \psi]\!] = \sup_{i \geq 0} \min\Big(\eta(i)\,[\![\pi^i, \psi]\!], \min_{0 \leq j < i} \eta(j)\,[\![\pi^j, \varphi]\!]\Big),
$$

and $[\![\pi, \varphi \oplus \psi]\!] = \tfrac{1}{2}\big([\![\pi, \varphi]\!] + [\![\pi, \psi]\!]\big)$.

**Validity.** The *validity problem* asks, given a formula $\varphi$ over $AP$ and a threshold $v \in [0,1]$, whether $[\![\pi, \varphi]\!] > v$ for every $\pi \in (2^{AP})^\omega$.

## Depends on

- [Formulas of linear temporal logic](../linear-temporal-logic/formula.md)

## Proof depends on

None.

## Expansion

On formulas without discounting operators the values are $0$ or $1$ and the semantics is that of LTL. The source shows that LTL can be augmented with an arbitrary set of discounting functions while preserving decidability of threshold model checking, since for a fixed threshold the discounting cuts the relevant horizon to a finite one and formulas translate to Büchi automata; the average operator breaks this.

## Sources

- S. Almagor, U. Boker and O. Kupferman, "Discounting in LTL", in *Tools and Algorithms for the Construction and Analysis of Systems (TACAS 2014)*, Lecture Notes in Computer Science 8413, Springer, 2014, pp. 424–439, doi:10.1007/978-3-642-54862-8_37; read as arXiv:1406.4249v2, <https://arxiv.org/abs/1406.4249v2>: Section 2 (discounting functions, syntax and semantics of discounted LTL) and the subsection "Adding the Average Operator" (the average operator and the validity problem).
