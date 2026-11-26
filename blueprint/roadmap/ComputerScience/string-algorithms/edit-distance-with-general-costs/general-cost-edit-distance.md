# Edit distance under general letter costs

A **cost function** on an alphabet $\Sigma$ assigns $\mathrm{del}(a) \ge 0$ to deleting $a$, $\mathrm{ins}(b) \ge 0$ to inserting $b$, and $\mathrm{sub}(a, b) \ge 0$ to replacing $a$ by $b$ (keeping $a$ costs $\mathrm{sub}(a, a)$, usually $0$). An **edit script** read left to right consumes a source word and produces a target word; its cost is the sum of its operation costs, and the **edit distance** $d(x, y)$ is the minimum cost of a script from $x$ to $y$. Scripts correspond to alignments of $x$ and $y$.

## Depends on

- [Edit script](../edit-distance/edit-script.md)

## Sources

- R. A. Wagner and M. J. Fischer, "The String-to-String Correction Problem", Journal of the ACM 21(1), 1974.
- J. Kleinberg and É. Tardos, "Algorithm Design", Addison-Wesley, 2006.
