# Reconstructed tree of a multi-type birth–death process

**Setting.** Let $\mathbf Z(t)=(Z_1(t),\dots,Z_k(t))$ be a multi-type birth–death process in which an individual of type $i$ gives birth to a type-$j$ individual at rate $b_i^{ij}$ (the parent keeps type $i$) and dies at rate $d_i$. Fix a time horizon $T>0$ and let $p_i(t,T)=\mathbb{P}[\mathbf Z(T)=0 \mid \mathbf Z(t)=\mathbf e_i]$ be the extinction probability by time $T$ of a single type-$i$ individual alive at time $t$. The **reconstructed (ancestral) process** $\mathbf W(t)$, $0\le t\le T$, counts by type the individuals alive at time $t$ that have descendants alive at time $T$; its tree is obtained by pruning every lineage with no extant descendant.

**Lemma 3.1.** $\mathbf W$ is a Markov process.

**Proposition 3.2.** $\mathbf W$ is a time-inhomogeneous multi-type pure birth process with type changes along lineages. At time $t\in[0,T)$ an individual of type $i$

- gives birth to a type-$j$ individual (both lineages surviving) at rate

$$q_i^{ij}(t) = b_i^{ij}\,\bigl(1-p_j(t,T)\bigr),$$

- changes into type $j\neq i$ (only the newborn lineage surviving) at rate

$$q_i^{j}(t) = b_i^{ij}\,\bigl(1-p_j(t,T)\bigr)\,\frac{p_i(t,T)}{1-p_i(t,T)}.$$

The extinction probabilities solve, for $i=1,\dots,k$,

$$-\frac{\partial p_i(t,T)}{\partial t} = d_i - \Bigl(\sum_{j=1}^k b_i^{ij}+d_i\Bigr)p_i(t,T) + \sum_{j=1}^k b_i^{ij}\,p_i(t,T)\,p_j(t,T),$$

with $p_i(T,T)=0$; the minus sign reflects that $t$ runs forward, so $p_i(t,T)$ decreases to $0$ as $t\uparrow T$ (for a pure death process $p(t,T)=1-e^{-d(T-t)}$). This corrects Remark 3.3 of arXiv:1409.2957, which prints this equation with the opposite sign on the left-hand side: its right-hand side is the derivative of $p_i$ in the remaining time $T-t$, not in $t$. With one type this reduces to the classical fact that the reconstructed tree of a birth–death process is a pure birth process with rate $b(1-p(t,T))$.

Unlike the single-type case, no deterministic time change turns the reconstructed process into a constant-rate multi-type Yule process, because the required time scale depends on the random type of the lineage that branches next; ignoring edge lengths therefore produces discrete trees with both binary and unary (type-change) branch points. Near the present, $p_i(t,T)\approx 0$, so $q_i^{ij}\approx b_i^{ij}$ and $q_i^{j}\approx 0$, which is what allows birth rates to be inferred from typed cherries near the tips.

## Expansion

Markovianity follows by induction over observation times from the branching property: given the population at time $t_1$, the subtrees of distinct individuals evolve independently, and an individual counted in $\mathbf W(t_1)$ is exactly one whose subtree survives to $T$. For the rates, a jump $\mathbf W\to\mathbf W+\mathbf e_j$ in $(t,t+\Delta t]$ requires a birth of type $j$ to a surviving type-$i$ individual with the newborn lineage also surviving, which has probability $\sum_i w_i b_i^{ij}(1-p_j)\Delta t$ after cancelling the survival factors of all other individuals. A jump $\mathbf W\to\mathbf W+\mathbf e_j-\mathbf e_i$ arises when a type-$i$ individual gives birth to type $j$ and only the newborn's lineage survives; conditioning the parent on survival introduces the ratio $p_i/(1-p_i)$.

## Sources

- Lea Popovic and Mariolys Rivas, "Topology and inference for multi-type Yule trees", arXiv:1409.2957 (2014), Section 3 (Lemma 3.1, Proposition 3.2, Remarks 3.3–3.4), <https://doi.org/10.48550/arXiv.1409.2957>. Published version: "Topology and inference for Yule trees with multiple states", Journal of Mathematical Biology 73(5) (2016), 1251–1291, <https://doi.org/10.1007/s00285-016-0992-6>; locators above refer to the arXiv version.
