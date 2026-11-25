# Same-name linear guards at a compatible interface communicate

Let $n$ be a natural number, $\Gamma$ a service environment, $\Lambda$, $\Theta$ ownership contexts
with disjoint domains such that $\Lambda \cup \Theta$ is semantically compatible, $a$ a name that is
not a declared trigger $\mathrm{c}_s$, and $g$, $h$ processes with $\Gamma; \Lambda \vdash_n g$ and
$\Gamma; \Theta \vdash_n h$ (runtime typing with shared services). If each of $g$ and $h$ is an
output $\overline{a}\langle b\rangle.p$ or an input $a(\cdot).p$ on $a$, then $g \mid h \to q$ for
some process $q$.
