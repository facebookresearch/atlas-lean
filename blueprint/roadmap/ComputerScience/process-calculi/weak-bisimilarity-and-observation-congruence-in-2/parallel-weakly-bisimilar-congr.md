# Parallel composition preserves weak bisimilarity in CCS with communication

Let the channel names form a type with decidable equality, and consider the finite CCS processes whose actions are CCS labels (the silent label $\tau$, inputs and outputs on names) with the transition relation of CCS with communication, in which an input and an output on the same name performed by the two components of a parallel composition synchronize to $\tau$. Write $P \Rightarrow P'$ when $P$ reaches $P'$ by zero or more $\tau$-transitions. A weak transition $P \stackrel{\mu}{\Longrightarrow} P'$ is either the trivial one $P \stackrel{\tau}{\Longrightarrow} P$ or a composite $P \Rightarrow P_1 \xrightarrow{\mu} P_2 \Rightarrow P'$. Two processes are weakly bisimilar, $P \approx Q$, when some bisimulation of the saturated system (same states, the weak transitions as transitions) relates them. For all processes $P_1, P_2, Q_1, Q_2$: if $P_1 \approx P_2$ and $Q_1 \approx Q_2$, then $P_1 \mid Q_1 \approx P_2 \mid Q_2$.

## Sources

- Robin Milner, *Communication and Concurrency*, Prentice Hall, 1989, Chapter 5 (ISBN 978-0-13-115007-2).
