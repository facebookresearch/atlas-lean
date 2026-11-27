# Baby steps

Let $q > 1$. Labels are elements of $\mathbb{Z}/q$, compared by decidable equality, and a query either multiplies two labels or inverts one. The baby-step loop with fuel $f$, current label $\mathit{cur}$, step label $g$ and accumulator list $\mathit{acc}$ is the oracle computation defined by recursion on $f$:

- with fuel $0$ it makes no query and returns $(\mathrm{reverse}(\mathit{acc}), \mathit{cur})$;
- with fuel $f + 1$ it queries the product of $\mathit{cur}$ and $g$, and on answer $\mathit{nxt}$ continues with fuel $f$, current label $\mathit{nxt}$, the same $g$ and the accumulator $\mathit{acc}$ with $\mathit{cur}$ prepended.

So each step records the current label and then makes one multiplication query. Against the oracle of an encoding permutation $\mathrm{enc}$ of $\mathbb{Z}/q$, starting from $\mathit{cur} = \mathrm{enc}(c)$, $g = \mathrm{enc}(1)$, the run returns $\mathrm{reverse}(\mathit{acc})$ followed by $\mathrm{enc}(c), \dots, \mathrm{enc}(c + f - 1)$, together with $\mathrm{enc}(c + f)$. The [baby-step giant-step algorithm](bsgs.md) uses $c = 0$, $\mathit{acc}$ empty and $f = m$, which gives the table $\mathrm{enc}(0), \dots, \mathrm{enc}(m - 1)$ and the final label $\mathrm{enc}(m)$; for other labels or oracles no such table is claimed.
