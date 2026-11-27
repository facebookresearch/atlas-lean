# Mutual exclusion from a test-and-set bit

In the asynchronous shared-memory model with a test-and-set bit $\mathit{lock}$, initially $0$, whose atomic operation $\mathrm{TAS}$ sets it to $1$ and returns its old value, and a reset operation that sets it to $0$, consider the protocol in which a trying process repeats $\mathrm{TAS}(\mathit{lock})$ until it returns $0$, then enters the critical region, and an exiting process resets $\mathit{lock}$. It solves the [mutual exclusion problem](the-mutual-exclusion-problem.md): it guarantees mutual exclusion and deadlock freedom. It is not starvation-free: a single fast process can win the bit every time while another process keeps trying.

## Depends on

- [The mutual exclusion problem](the-mutual-exclusion-problem.md)

## Sources

- J. Aspnes, *Notes on Theory of Distributed Systems*, arXiv:2001.04235v6 (18 May 2026), <https://arxiv.org/abs/2001.04235v6>, Section 18.3.1 ("Test and set") and Algorithm 18.1, with the arguments for mutual exclusion and progress and the failure of starvation-freedom, pp. 152–153.
