# Ideal 1-out-of-2, batched and 1-out-of-4 oblivious transfer

The *1-out-of-2 oblivious transfer* functionality over a value set $M$ takes from the sender a pair $(m_0, m_1) \in M^2$ and from the receiver a bit $c$, gives $m_c$ to the receiver and nothing to the sender. *Batched* oblivious transfer performs $k$ such transfers in one invocation (sender input $(m_{j,0}, m_{j,1})_{j<k}$, receiver input $c \in \{0,1\}^k$). The *1-out-of-4* transfer $\mathrm{OT}^4_1$ of bits takes a table $(t_0, t_1, t_2, t_3)$ from the sender and an index $i \in \{0, \dots, 3\}$ from the receiver and returns $t_i$. A protocol in the *$\mathcal{F}$-hybrid model* may call an ideal functionality $\mathcal{F}$ as an oracle whose answers are delivered privately to the parties; its semi-honest security is defined by simulation of the joint views and outputs as in the plain model, with each party's view including the oracle answers addressed to it.

## Depends on

- [Two-party security against semi-honest adversaries](../two-party-security-against-semi-honest.md)
- [Multiparty security against semi-honest adversaries](../multiparty-security-against-semi-honest.md)
- [Oblivious transfer from the decisional Diffie–Hellman assumption](../oblivious-transfer-from-the-decisional.md)

## Sources

- Oded Goldreich, "Foundations of Cryptography, Volume 2: Basic Applications", Cambridge University Press, 2004.
- Moni Naor and Benny Pinkas, "Efficient Oblivious Transfer Protocols", Proceedings of the Twelfth Annual ACM-SIAM Symposium on Discrete Algorithms, 2001.
