# Semantics of release

For a valuation of atoms on letters, an ω-word $w$ and LTL formulas
$\varphi$ and $\psi$, $w$ satisfies $\varphi \mathbin{\mathsf{R}} \psi$ ($\varphi$ releases $\psi$)
if and only if for every position $k$, either $\psi$ holds at position $k$ of $w$ or $\varphi$
holds at some position $j < k$ of $w$.
