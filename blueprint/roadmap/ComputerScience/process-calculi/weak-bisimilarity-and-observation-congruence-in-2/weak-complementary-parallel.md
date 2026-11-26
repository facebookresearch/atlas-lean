# Complementary weak transitions synchronize to silent steps in CCS with communication

Let the channel names form a type with decidable equality, and consider the finite CCS processes whose actions are CCS labels (the silent label $\tau$, inputs and outputs on names) with the transition relation of CCS with communication, in which an input and an output on the same name performed by the two components of a parallel composition synchronize to $\tau$. Write $P \Rightarrow P'$ when $P$ reaches $P'$ by zero or more $\tau$-transitions. A weak transition $P \stackrel{\mu}{\Longrightarrow} P'$ is either the trivial one $P \stackrel{\tau}{\Longrightarrow} P$ or a composite $P \Rightarrow P_1 \xrightarrow{\mu} P_2 \Rightarrow P'$. Two labels are complementary when one is the input and the other the output on the same name; $\tau$ is complementary to no label. If $P \stackrel{\alpha}{\Longrightarrow} P'$ and $Q \stackrel{\beta}{\Longrightarrow} Q'$ with $\alpha$ and $\beta$ complementary, then $P \mid Q \Rightarrow P' \mid Q'$.

## Sources

- Robin Milner, *Communication and Concurrency*, Prentice Hall, 1989, Chapter 5 (ISBN 978-0-13-115007-2).
