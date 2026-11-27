# Byzantine agreement with signed messages

There are $n$ generals: a commander, General $0$, and $n - 1$ lieutenants. At most $m$ generals, including the commander if faulty, are traitors. Loyal generals follow the algorithm and
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
2. lieutenant $i$ handles the two kinds of receipt separately:
    - If $i$ receives a verified bare order $v : 0$ directly from the commander and $V_i$ is empty, $i$ sets $V_i = \{v\}$ and sends $v : 0 : i$ to every other lieutenant.
    - If $i$ receives a properly signed chain $v : 0 : j_1 : \cdots : j_k$ with $k \ge 1$ and $v \notin V_i$, $i$ adds $v$ to $V_i$. If $k < m$, $i$ sends the chain with $i$ appended to every lieutenant other than $i$ and the earlier signers $j_1, \dots, j_k$;
3. when he will receive no more messages, lieutenant $i$ obeys $\mathrm{choice}(V_i)$.

**Theorem.** For every $m$, if there are at most $m$ traitors, $\mathrm{SM}(m)$ satisfies the interactive consistency conditions:

- IC1: all loyal lieutenants obey the same order;
- IC2: if the commander is loyal, every loyal lieutenant obeys the order he sends.

## Scope of the model

A completed history is a finite sequence of abstract send and receipt events. The immediate
sender is recorded separately from the signers. Send and receipt obligations match the full
message, not a unique transmission identifier; repeated copies of a value do not add it again.
A verified chain containing a loyal signature must have a prior send by that signer of the
exact corresponding signed prefix. No such provenance is required of a faulty signer.

The cutoff applies to forwarding nonempty chains, not to accepting them. A first bare order
from the commander is forwarded even when $m=0$. At the cutoff with a faulty commander, the
chain includes a loyal lieutenant, because its distinct signers together with the commander
outnumber the faults. That lieutenant must have accepted the shorter prefix and followed the
forwarding rule. The result assumes the reception history is complete; it neither constructs
a termination detector nor implements signatures.

## Sources

- L. Lamport, R. Shostak and M. Pease, "The Byzantine generals problem", *ACM Transactions on Programming Languages and Systems* 4(3):382–401, 1982, <https://lamport.azurewebsites.net/pubs/byz.pdf>: Section 1 (IC1 and IC2), Section 3 (assumptions A1–A3), Section 4 (assumption A4, the function choice, algorithm SM(m) and Theorem 2).
