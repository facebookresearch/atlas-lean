# delta-weakening and delta-complete decision procedures

Consider bounded existential formulas $\varphi$ over the reals in which every variable ranges
over a closed box with rational endpoints, and the matrix is a positive Boolean combination of atoms $t > 0$, $t \ge 0$ and
$t = 0$, where the terms $t$ are built from functions computable and total on the box. For rational $\delta > 0$, the
δ-weakening $\varphi^\delta$ replaces $t > 0$ by $t > -\delta$, $t \ge 0$ by $t \ge -\delta$ and $t = 0$ by $\lvert t \rvert \le \delta$. A
δ-complete decision procedure returns either "unsat", only if $\varphi$ is unsatisfiable, or "δ-sat", only if $\varphi^\delta$ is
satisfiable; when $\varphi$ is unsatisfiable and $\varphi^\delta$ is satisfiable, both answers are correct. That $\varphi$
implies $\varphi^\delta$, and $\varphi^\delta$ implies $\varphi^{\delta'}$ for $\delta \le \delta'$, are separate lemmas. The source
states the definition for its standard form, in which every atom is an equation $f = 0$ and $\varphi^\delta$ replaces it by
$\lvert f \rvert \le \delta$; atoms $t \ge 0$ and $t > 0$ enter that form as $t - v = 0$ with a new variable $v$ bounded in $[0, m]$
or $(0, m]$ for some $m$ above the maximum of $t$ on the box, which gives exactly the relaxations above.

## Sources

- delta-Complete Decision Procedures for Satisfiability over the Reals — S. Gao, J. Avigad, E. M. Clarke, LNAI 7364, 2012, Definition 2.5, Lemma 2.1, Definitions 3.1 and 3.2 and Proposition 3.1. <http://www.cs.cmu.edu/~sicung/papers/cade2012.pdf>
