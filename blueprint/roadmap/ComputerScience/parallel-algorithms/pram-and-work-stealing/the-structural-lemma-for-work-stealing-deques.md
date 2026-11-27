# The structural lemma for work-stealing deques

Consider an execution of the non-blocking work stealer of Arora, Blumofe and Plaxton on a multithreaded computation, whose enabling tree has an edge from each node to the node whose execution enabled it (its designated parent). At any time, let a process's deque contain nodes $v_1, \dots, v_k$ from bottom to top, let $v_0$ be its assigned node if it has one, and suppose none of these is the root, so each $v_i$ has a designated parent $u_i$. Then for each $i \ge 1$ for which $u_{i-1}$ is defined ($i \ge 1$ if there is an assigned node, $i \ge 2$ otherwise), $u_i$ is an ancestor of $u_{i-1}$ in the enabling tree, properly for $i \ge 2$, while $u_1 = u_0$ is allowed; equivalently the defined designated parents $u_k, \dots, u_1(, u_0)$ lie in this order on a root-to-leaf path.

## Expansion

This page becomes ready once these prerequisites are stated:

- Multithreaded computations with enabling edges and the non-blocking work-stealing deque execution (statement prerequisite)

## Sources

- N. S. Arora, R. D. Blumofe and C. G. Plaxton, "Thread scheduling for multiprogrammed multiprocessors", *Theory of Computing Systems* 34(2):115–144, 2001
- R. D. Blumofe and C. E. Leiserson, "Scheduling multithreaded computations by work stealing", *Journal of the ACM* 46(5):720–748, 1999
