# Work-conserving schedulers keep pace with any schedule on a slower platform

Let $\pi$ be a [uniform multiprocessor platform](uniform-multiprocessor-platforms.md) with cumulative capacity $S_\pi$ and fastest speed $s_\pi < 1$, and let $\pi'$ consist of $m'$ identical unit-speed processors with

$$
m' \ge \frac{S_\pi - s_\pi}{1 - s_\pi} .
$$

Then for every algorithm $A$ on $\pi$, every work-conserving algorithm $A'$ on $\pi'$, every set $I$ of jobs and every $t \ge 0$: $W(A', \pi', I, t) \ge W(A, \pi, I, t)$.

**Proof sketch.** Otherwise take a job $J_j$ of earliest arrival on which $A'$ has done less work than $A$ by some $t_0$ while $W(A', \pi', I, t_0) < W(A, \pi, I, t_0)$. Over $[r_j, t_0)$ let $x$ be the time $A'$ keeps all $m'$ processors busy and $y$ the rest. Being work-conserving, $A'$ runs $J_j$ for at least $y$, while $A$ runs it for at most $x + y$ at speed at most $s_\pi$, so $(x + y)s_\pi > y$; and $S_\pi(x + y) > m'x + y$. Adding $(m' - 1)$ times the first to the second gives $(S_\pi - s_\pi)/(1 - s_\pi) > m'$.

## Depends on

- [Uniform multiprocessor platforms](uniform-multiprocessor-platforms.md)

## Sources

- J. Goossens, S. Funk and S. Baruah, *Priority-driven scheduling of periodic task systems on multiprocessors*, technical report TR01-024, Department of Computer Science, University of North Carolina at Chapel Hill, <http://www.cs.unc.edu/techreports/01-024.pdf>; published in *Real-Time Systems* 25(2–3):187–205, 2003; the section, theorem and footnote numbers below are those of the technical report, Section 3, Lemma 1 with its proof (inequalities (3)–(6)).
