# Synchronous Byzantine agreement protocol

A synchronous Byzantine agreement protocol $Q$ for a set $G$ of processes, a set $V$ of inputs, a set $\sigma$ of local states and a set $M$ of messages consists of maps $\mathrm{init} : G \times V \to \sigma$, $\mathrm{send} : \mathbb{N} \times G \times \sigma \times G \to M$, $\mathrm{recv} : \mathbb{N} \times G \times \sigma \times M^G \to \sigma$ and $\mathrm{decide} : G \times \sigma \to V$. Process $i$ starts in state $\mathrm{init}(i, x)$ from its input $x$; in each round $r$ every process $j$ in state $s$ sends $\mathrm{send}(r, j, s, i)$ to every process $i$, and then process $i$ in state $s$ moves to $\mathrm{recv}(r, i, s, \mathit{msg})$, where $\mathit{msg}(j)$ is the message it received from $j$; at the end process $i$ in state $s$ decides $\mathrm{decide}(i, s)$.

**Model.** Synchronous lock-step rounds; every process sends one message to every process (itself included) in each round, over a complete network of reliable links; a receiver knows the sender of each message; there are no signatures. Protocols are deterministic, with one set of states for all processes, which loses no generality (take a disjoint union). Faulty processes are modelled in [Executions of a Byzantine agreement protocol](state.md).

## Background

- [Oral-message protocol](../byzantine-generals-problem/oral-protocol.md): the same round structure for the commander version, where only the commander has an input.
