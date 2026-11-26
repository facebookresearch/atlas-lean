# The parallel lift of weak simulations is a weak simulation in CCS with communication

Let the channel names form a type with decidable equality, and consider the finite CCS processes whose actions are CCS labels (the silent label $\tau$, inputs and outputs on names) with the transition relation of CCS with communication, in which an input and an output on the same name performed by the two components of a parallel composition synchronize to $\tau$. Write $P \Rightarrow P'$ when $P$ reaches $P'$ by zero or more $\tau$-transitions. A weak transition $P \stackrel{\mu}{\Longrightarrow} P'$ is either the trivial one $P \stackrel{\tau}{\Longrightarrow} P$ or a composite $P \Rightarrow P_1 \xrightarrow{\mu} P_2 \Rightarrow P'$. A relation $R$ is a simulation of the saturated system when, whenever $R$ relates $U$ to $V$ and $U \stackrel{\mu}{\Longrightarrow} U'$, there is $V'$ with $V \stackrel{\mu}{\Longrightarrow} V'$ and $R$ relating $U'$ to $V'$. The parallel lift of relations $R$ and $S$ relates $U$ to $V$ exactly when $R$ relates them, or $S$ relates them, or $U = P_1 \mid Q_1$ and $V = P_2 \mid Q_2$ with $R$ relating $P_1$ to $P_2$ and $S$ relating $Q_1$ to $Q_2$. If $R$ and $S$ are simulations of the saturated system, then so is their parallel lift.

## Sources

- Robin Milner, *Communication and Concurrency*, Prentice Hall, 1989, Chapter 5 (ISBN 978-0-13-115007-2).
