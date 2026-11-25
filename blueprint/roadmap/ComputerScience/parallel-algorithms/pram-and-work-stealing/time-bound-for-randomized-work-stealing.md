# Time bound for randomized work stealing

A multithreaded computation is a dag of unit-time instructions grouped into threads, with spawn edges from a thread to the threads it
spawns and join edges between threads; its work $T_1$ is the number of nodes and its span (critical-path length) $T_\infty$ the number of
nodes on a longest directed path. It is *fully strict* if every join edge from a thread goes to the thread's parent in the spawn tree.

- **Dedicated processors.** For every fully strict multithreaded computation, the randomized work-stealing algorithm of Blumofe and
  Leiserson on $P$ processors runs in expected time $T_1/P + O(T_\infty)$, including scheduling overhead, and for every $\varepsilon > 0$ in time
  $T_1/P + O(T_\infty + \lg P + \lg(1/\varepsilon))$ with probability at least $1 - \varepsilon$. The expected number of steal attempts is $O(P\,T_\infty)$.
- **Multiprogrammed environments.** Let $P_A$ be the time-average number of processors on which the kernel runs the computation's $P$
  processes. The non-blocking work stealer of Arora, Blumofe and Plaxton executes any multithreaded computation in expected time
  $O(T_1/P_A + T_\infty P/P_A)$, and in time $O(T_1/P_A + (T_\infty + \lg(1/\varepsilon)) P/P_A)$ with probability at least $1 - \varepsilon$, in each of these
  settings: a benign adversary kernel with a yield call that does nothing; an oblivious adversary with yieldToRandom; and an adaptive
  adversary with yieldToAll. On dedicated processors its expected time is $O(T_1/P + T_\infty)$.

## Proof depends on

- [The structural lemma for work-stealing deques](the-structural-lemma-for-work-stealing-deques.md)

## Sources

- R. D. Blumofe and C. E. Leiserson, "Scheduling multithreaded computations by work stealing", *Journal of the ACM* 46(5):720–748, 1999: Section 2 (work, span, fully strict computations), Theorem 13 and Lemma 12 (the bound on steal attempts).
- N. S. Arora, R. D. Blumofe and C. G. Plaxton, "Thread scheduling for multiprogrammed multiprocessors", *Theory of Computing Systems* 34(2):115–144, 2001: Section 1 (the average processor count $P_A$), Theorems 9–12.
