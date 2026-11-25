# Asynchronous message-passing systems

In an asynchronous message-passing system, $n$ processes are nodes of a directed communication network, and each edge from $p_i$ to $p_j$ carries a channel $b_{ij}$, the multiset of messages sent from $p_i$ to $p_j$ but not yet delivered. Each process is deterministic: its transition function maps its state and a multiset of incoming messages to a new state and a multiset of messages to send to its out-neighbors. A *delivery event* removes some messages from channels into $p_j$, delivers them to $p_j$, updates its state and adds its outgoing messages to its channels; a *computation event* does the same with no messages delivered. A *configuration* gives the state of every process and channel, and an *execution* is a sequence $C_0, \varphi_1, C_1, \varphi_2, \dots$ of configurations and events, starting from an initial configuration, in which each $C_{i+1}$ results from applying $\varphi_{i+1}$ to $C_i$.

There is no bound on message delay or on the relative speed of processes. With *reliable channels*, an infinite execution is *admissible* if every process takes infinitely many computation steps and every message sent is eventually delivered. With *lossy channels*, the second condition is dropped: a message that is sent may never be delivered.

## Sources

- J. Aspnes, *Notes on Theory of Distributed Systems*, Yale University, 2020, <https://arxiv.org/abs/2001.04235>, the chapter "Model" of Part I (the basic message-passing model and asynchronous systems)
- S. Gilbert and N. Lynch, "Brewer's conjecture and the feasibility of consistent, available, partition-tolerant web services", *ACM SIGACT News* 33(2):51–59, 2002, Sections 2.3 and 3.1 (messages that are sent may be lost)
