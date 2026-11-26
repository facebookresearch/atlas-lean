# Obs RY nonresponse Shift

Full-data laws are measures on $\{0,1\} \times \mathbb R$, a point $(r, y)$ recording the response indicator $r$ ($r = 1$ for a respondent) and the outcome $y$. The observed data of $(r, y)$ are $o(r, y) = (r, y)$ if $r = 1$ and $o(r, y) = (0, 0)$ if $r = 0$; the observed-data law of $P$ is the pushforward $P \circ o^{-1}$. For $\delta \in \mathbb R$ let $s_\delta$ be the $\delta$-shift of nonrespondents, $s_\delta(r, y) = (r, y)$ if $r = 1$ and $s_\delta(r, y) = (r, y + \delta)$ if $r = 0$. Then for every $\delta$ and every $(r, y)$,

$$o\bigl(s_\delta(r, y)\bigr) = o(r, y),$$

so the $\delta$-shift does not change the observed data.
