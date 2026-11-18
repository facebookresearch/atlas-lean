# Satisfaction of LTL formulas on ω-words

Let $v$ be a valuation that says which atoms are
true at each letter, and for an ω-word $w$ and a natural number $k$ let $w^{(k)}$ be the suffix
$i \mapsto w(k + i)$. Whether $w$ satisfies an LTL formula $\varphi$ under $v$, written
$w \models \varphi$, is defined by recursion on $\varphi$: an atom $a$ holds when $v$ makes $a$
true at the first letter $w(0)$; truth always holds; $\neg \varphi$ holds when $\varphi$ does
not; $\varphi \wedge \psi$ holds when both $\varphi$ and $\psi$ do; $\mathsf{X}\, \varphi$ (next
$\varphi$) holds when $w^{(1)} \models \varphi$; and $\varphi \mathbin{\mathsf{U}} \psi$
($\varphi$ until $\psi$) holds when there is a $k$ with $w^{(k)} \models \psi$ and
$w^{(j)} \models \varphi$ for all $j < k$.
