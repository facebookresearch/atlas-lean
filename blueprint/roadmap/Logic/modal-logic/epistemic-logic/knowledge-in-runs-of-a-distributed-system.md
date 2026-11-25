# Knowledge in runs of a distributed system

A distributed system consists of processors that communicate by sending messages. A *run* of a protocol is one possible execution, which fixes the messages sent and the messages delivered, and when. A *point* is a pair $(r, t)$ of a run and a time. At a point, each processor $i$ has a *local state*: its initial state, its clock time, and its message history, the sequence of messages it has sent and received with the times on its clock at which it sent or received them.

The *interpreted system* of the protocol is the multi-agent Kripke model with the following ingredients:
- **worlds:** the points of all runs;
- **accessibility:** $(r, t)\, R_i\, (r', t')$ when processor $i$ has the same local state at both points;
- **valuation:** each fact $p$ is true at a set of points.

Then:
- $K_i\, p$ holds at $(r, t)$ when $p$ holds at every point $i$ cannot distinguish from $(r, t)$;
- $E_G$ and [common knowledge](common-knowledge-as-a-greatest-fixed-point.md) $C_G$ are evaluated in this model;
- a fact is *stable* if, once true in a run, it stays true.

Halpern and Moses describe knowledge through deduction. Processors draw only sound conclusions from their information, never forget, and send a message stating $p$ only if they know $p$. Processor $i$ *supports* $C p$ if it knows every formula $K_{i_1} \cdots K_{i_n} p$, and the system has *attained* $C p$ when all processors support it. In a knowledge-consistent system, one processor supports $C p$ if and only if the system has attained it.

The accessibility relations $R_i$ are equivalence relations, so knowledge in interpreted systems satisfies the axioms of the modal logic S5 for each agent.

## Depends on

- [Common knowledge as a greatest fixed point](common-knowledge-as-a-greatest-fixed-point.md)

## Expansion

This page becomes ready once these are stated:

- the formal model of runs over a fixed message-passing execution model, including clocks and the delivery assumptions (guaranteed or not, bounded delay), as a source-backed definition (statement prerequisite; source not yet opened);
- the correspondence between the deduction-based description of knowledge and the indistinguishability semantics (proof prerequisite; not yet stated).

## Sources

- J. Y. Halpern and Y. Moses, "Knowledge and common knowledge in a distributed environment", *Proceedings of the 3rd ACM Symposium on Principles of Distributed Computing (PODC)*, 1984, pp. 50–61, <https://groups.csail.mit.edu/tds/papers/Halpern/podc84.pdf>, Sections 2–3: processors with internal state and message history, sound deduction, no forgetting and honesty, knowledge $K_i p$, protocols and runs, supporting and attaining $C p$, knowledge consistency, and Lemma 1.
- R. Fagin, J. Y. Halpern, Y. Moses and M. Y. Vardi, *Reasoning About Knowledge*, MIT Press, 1995 (not opened).
