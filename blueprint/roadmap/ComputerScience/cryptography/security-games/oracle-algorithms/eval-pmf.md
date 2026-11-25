# Running an oracle computation against a randomized oracle

Let $c$ be an adaptive oracle computation whose queries $a$ have answers in sets $B_a$, and let $O$
be a randomized oracle, giving for each query $a$ a probability distribution $O(a)$ on $B_a$. The
run of $c$ against $O$ is the distribution of its output when every query $a$ is answered by a
fresh sample of $O(a)$: Katz and Lindell's oracle access to a randomized algorithm (Section 3.4.2).
