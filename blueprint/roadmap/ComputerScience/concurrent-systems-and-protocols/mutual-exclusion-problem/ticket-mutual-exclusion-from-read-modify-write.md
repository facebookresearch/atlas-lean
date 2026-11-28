# Starvation-free mutual exclusion from a read-modify-write register

In the asynchronous shared-memory model with a read-modify-write register $V$ holding two counters $\mathit{first}$ and $\mathit{last}$, both initially $0$, consider the protocol in which a trying process atomically increments $V.\mathit{last}$ and remembers its old value $\ell$, waits until it reads $V.\mathit{first} = \ell$, then enters the critical region, and an exiting process atomically increments $V.\mathit{first}$. It solves the [mutual exclusion problem](the-mutual-exclusion-problem.md) and is starvation-free; indeed it has bounded bypass: once a process has taken its ticket, no other process enters the critical region twice before it does.

## Depends on

- [The mutual exclusion problem](the-mutual-exclusion-problem.md)

## Sources

- J. Aspnes, *Notes on Theory of Distributed Systems*, arXiv:2001.04235v6 (18 May 2026), <https://arxiv.org/abs/2001.04235v6>, Section 18.3.2 (the queue-based algorithm, Algorithm 18.2, and its invariants for mutual exclusion, deadlock freedom, starvation-freedom and bounded bypass) and Section 18.3.2.1 ("Replacing the queue with RMW", Algorithm 18.3), pp. 153–155.
