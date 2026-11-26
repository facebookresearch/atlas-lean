# Splitting off the head of a segment

Let $p_0$ be a model-checking game position and $\pi$
an infinite sequence of positions of the totalized fragment game. For each $i$, let $\hat\pi_i$ be
$p_0$ if $\pi_i$ is an absorbing state; if $\pi_i$ is the embedded position $(\varphi, w)$ of a
fixpoint-free formula $\varphi$ and a world $w$, let $\hat\pi_i$ be the game position
$(\varphi, w, [])$, with $\varphi$ embedded as a μ-calculus formula and the empty fixpoint stack.
For all natural numbers $s$ and $k$, the segment $[\hat\pi_s, \dots, \hat\pi_{s+k+1}]$ of $\pi$ is
the list with head $\hat\pi_s$ followed by the segment $[\hat\pi_{s+1}, \dots, \hat\pi_{s+k+1}]$.
