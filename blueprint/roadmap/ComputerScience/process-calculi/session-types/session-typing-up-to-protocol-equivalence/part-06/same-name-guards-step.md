# Same-name conversion guards are opposite and communicate

Let $n$ be a natural number, $\Gamma$, $\Theta$ ownership contexts with disjoint domains such that
$\Gamma \cup \Theta$ is semantically compatible, $a$ a name and $g$, $h$ processes with $\Gamma
\vdash^{\mathrm{rk}\simeq}_n g$ and $\Theta \vdash^{\mathrm{rk}\simeq}_n h$. If each of $g$ and $h$
is an output $\overline{a}\langle b\rangle.p$ or an input $a(\cdot).p$ on the same name $a$, then $g
\mid h$ reduces in one π-calculus step to some process.
