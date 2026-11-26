# The nonblocking progress hierarchy is strict

For asynchronous shared-memory implementations, wait-freedom implies lock-freedom, which implies obstruction-freedom. The inclusions are strict: an atomic fetch-and-increment counter is wait-free, while a compare-and-swap retry-loop counter is lock-free but not wait-free (a process can starve forever while others succeed), and Treiber's stack is lock-free.

## Proof sketch

In an infinite execution where some pending operation keeps taking steps, wait-freedom completes it; a failed compare-and-swap witnesses an intervening successful one, which gives lock-freedom; an adversarial schedule interleaving one slow process with successful competitors refutes wait-freedom.

## Depends on

- [Progress conditions for concurrent implementations](../progress-conditions-for-concurrent.md)

## Proof depends on

- [Weak and strong fairness](../../distributed-execution-models/weak-and-strong-fairness.md)

## Sources

- Maurice Herlihy, "Wait-Free Synchronization", ACM Transactions on Programming Languages and Systems, 1991.
- Maurice Herlihy, Victor Luchangco and Mark Moir, "Obstruction-Free Synchronization: Double-Ended Queues as an Example", 23rd International Conference on Distributed Computing Systems (ICDCS), 2003.
- Mark Moir and Nir Shavit, "Concurrent Data Structures", Handbook of Data Structures and Applications, Chapman and Hall/CRC, 2004.
- R. Kent Treiber, "Systems Programming: Coping with Parallelism", IBM Almaden Research Center, 1986.
