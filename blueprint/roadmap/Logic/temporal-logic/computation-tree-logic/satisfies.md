# Satisfaction of CTL formulas

Fix a labelled transition system and a valuation saying
which atoms hold at which states. Satisfaction of a CTL formula at a state $s$ is defined by
recursion on the formula. An atom $a$ holds at $s$ when the valuation makes $a$ true at $s$;
$\top$ always holds; $\neg\varphi$ holds when $\varphi$ does not; $\varphi \land \psi$ holds
when both $\varphi$ and $\psi$ hold; $\mathsf{EX}\,\varphi$ holds when there is a transition
from $s$, under some label, to a state satisfying $\varphi$; $\mathsf{E}[\varphi\,\mathsf{U}\,\psi]$
holds when some finite run $s = s_0, s_1, \dots, s_k$ has $\psi$ at $s_k$ and $\varphi$ at every
$s_j$ with $j < k$; $\mathsf{EG}\,\varphi$ holds when some infinite run $s = s_0, s_1, \dots$ has
$\varphi$ at every state; and $\mathsf{A}[\varphi\,\mathsf{U}\,\psi]$ holds when, first, every
infinite run $s = s_0, s_1, \dots$ has some $k$ with $\psi$ at $s_k$ and $\varphi$ at every $s_j$
with $j < k$, and second, every finite run $s = s_0, s_1, \dots, s_k$ whose last state $s_k$ has
no outgoing transition under any label has some $j \le k$ with $\psi$ at $s_j$ and $\varphi$ at
every $s_i$ with $i < j$.
