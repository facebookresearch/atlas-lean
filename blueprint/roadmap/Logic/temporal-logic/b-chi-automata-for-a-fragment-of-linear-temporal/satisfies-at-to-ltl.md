# Propositional formulas are evaluated at the current letter

Let $\varphi$ be a
propositional formula, let $w = w_0 w_1 w_2 \dots$ be an ω-word whose letters are sets of atoms,
and let $k \in \mathbb{N}$. Under the valuation in which an atom holds at a letter exactly when it
belongs to that letter, the LTL translation of $\varphi$ holds at position $k$ of $w$ if and only
if $\varphi$ evaluates to true on the letter $w_k$.
