# Own-entry comparison detects happened-before

Let $a$ and $b$ be positions of events of
an execution, and let $p$ be the process of the event at $a$. If the $p$-entry of the vector
timestamp of $a$ is at most the $p$-entry of the vector timestamp of $b$, then $a = b$ or $a$
happened before $b$.
