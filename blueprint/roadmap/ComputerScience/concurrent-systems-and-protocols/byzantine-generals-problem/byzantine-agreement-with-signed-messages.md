# Byzantine agreement with signed messages

There are $n$ generals: a commander, General $0$, and $n - 1$ lieutenants, of whom at most $m$ are traitors. Loyal generals follow the algorithm and
traitors behave arbitrarily. Messages satisfy:

- A1: every message that is sent is delivered correctly;
- A2: the receiver of a message knows who sent it;
- A3: the absence of a message can be detected;
- A4: (a) a loyal general's signature cannot be forged, and any alteration of the contents of a message he signed can be detected;
  (b) anyone can verify the authenticity of a general's signature. Nothing is assumed about traitors' signatures, which other traitors
  may forge.

Write $v : i$ for the value $v$ signed by General $i$. A message $v : 0 : j_1 : \cdots : j_k$ received by lieutenant $i$ is *properly signed* if every signature in it is authentic and $j_1, \dots, j_k$ are pairwise distinct lieutenants, all different from $i$; messages with repeated signers are discarded. Fix a function $\mathrm{choice}$ on finite sets of orders with $\mathrm{choice}(\{v\}) = v$ and
$\mathrm{choice}(\emptyset) = \mathrm{RETREAT}$. In algorithm $\mathrm{SM}(m)$ each lieutenant $i$ keeps a set $V_i$ of orders, initially empty:

1. the commander signs his order and sends it to every lieutenant;
2. if lieutenant $i$ receives $v : 0$ from the commander and has no order yet, he sets $V_i = \{v\}$ and sends $v : 0 : i$ to every other lieutenant; if he
   receives a properly signed $v : 0 : j_1 : \cdots : j_k$ with $v \notin V_i$, he adds $v$ to $V_i$ and, if $k < m$, sends $v : 0 : j_1 : \cdots : j_k : i$ to every lieutenant
   other than $j_1, \dots, j_k$;
3. when he will receive no more messages, lieutenant $i$ obeys $\mathrm{choice}(V_i)$.

**Theorem.** For every $m$, if there are at most $m$ traitors, $\mathrm{SM}(m)$ satisfies the interactive consistency conditions:

- IC1: all loyal lieutenants obey the same order;
- IC2: if the commander is loyal, every loyal lieutenant obeys the order he sends.

## Sources

- L. Lamport, R. Shostak and M. Pease, "The Byzantine generals problem", *ACM Transactions on Programming Languages and Systems* 4(3):382–401, 1982, <https://lamport.azurewebsites.net/pubs/byz.pdf>: Section 1 (IC1 and IC2), Section 3 (assumptions A1–A3), Section 4 (assumption A4, the function choice, algorithm SM(m) and Theorem 2).
