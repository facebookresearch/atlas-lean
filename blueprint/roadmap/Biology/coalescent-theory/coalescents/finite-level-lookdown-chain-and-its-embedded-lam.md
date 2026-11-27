# The first n lookdown levels have Kingman's coalescent as genealogy

Fix integers $0\le n\le N$ with $N\ge1$ and a deterministic observation time $T\ge0$. In the [finite shifting lookdown process](../../population-genetics/diffusion-theory/fleming-viot-processes/finite-level-lookdown-process-and-projective-con.md), each pair $i<j$ has an independent rate-one reproduction clock. Trace the neutral ancestry of the individuals at levels $1,\ldots,n$ at time $T$ backward over $[0,T]$. Mutations do not merge or relocate ancestral lines. Individuals with equal types are not thereby identified as ancestors. No exchangeability assumption on initial types is needed for this genealogical statement.

At a forward reproduction arrow $i\to j$, the map from post-event levels to their pre-event parents is

$$a_{ij}(\ell)=\begin{cases}\ell,&\ell<j,\\i,&\ell=j,\\\ell-1,&\ell>j.\end{cases}$$

Let $A_k^T(s)$ be the ancestral level of sampled individual $k$ at forward time $s\le T$. With Birkner's convention, $A_k^T(s)$ crosses the arrows in $(s,T]$, so it is right-continuous in $s$. The partition

$$k\sim_{R_n(v)}\ell\quad\Longleftrightarrow\quad A_k^T(T-v)=A_\ell^T(T-v),\qquad 0\le v\le T,$$

is consequently left-continuous in backward elapsed time $v$, as stated in Birkner's Remark 1.5.3. Its right-continuous version $\widehat R_n$ applies each merger at the corresponding backward event time. Equivalently, take the right limit for $v<T$ and the same terminal value at $T$. Since the observation time is deterministic and Poisson clocks have no atoms at deterministic times, these versions agree almost surely at every fixed deterministic $v$. They need not agree at the random merger times.

The process $\widehat R_n$, started from the singleton partition and restricted to $[0,T]$, is Kingman's $n$-coalescent, with the [partition rate matrix](../partition-valued-kingman-coalescent/partition-rate.md):

$$Q_n(\pi,\pi')=\begin{cases}1,&\pi'\text{ merges exactly two blocks of }\pi,\\-\binom{|\pi|}{2},&\pi'=\pi,\\0,&\text{otherwise}.\end{cases}$$

The empty sample and the one-block partition are absorbing. In particular the two-lineage merger time in the continued coalescent has law $\operatorname{Exp}(1)$; within the observed interval its survival probability at $0\le v\le T$ is $e^{-v}$. There are no simultaneous multiple mergers. The genealogy of the first $n$ levels is independent of the ambient size $N\ge n$, and restriction to a smaller sampled prefix gives that prefix's genealogy.

## Proof for the shifting convention

Initially the distinct ancestral levels are exactly $1,\ldots,n$. If they are $1,\ldots,m$, an arrow with $j>m$ leaves them unchanged. An arrow with $j\le m$ merges precisely the blocks at levels $i$ and $j$ and shifts the higher ancestral levels down, leaving the occupied prefix $1,\ldots,m-1$. Thus the prefix property holds throughout the backward construction. It concerns distinct ancestral levels, not the number of original sample labels within each block.

Time reversal on the fixed deterministic interval $[0,T]$ preserves the joint law of the independent homogeneous Poisson clocks. With $m$ blocks, each unordered pair occupies exactly one pair of current levels $i<j\le m$ and has merger rate one. The total merger rate is $\binom m2$, and the next pair is uniform. The resulting finite-state partition chain therefore has generator $Q_n$. Arrows targeted above $n$ never affect this backward construction, giving the common-clock identification between ambient sizes for the shifting model. Restricting sampled labels commutes with their ancestral maps.

## Genealogy-only bridge to the non-shifting convention

Etheridge's Definition 2.1 instead overwrites level $j$ with the type at level $i$ and leaves all other levels in place. Its backward parent map is

$$b_{ij}(\ell)=\begin{cases}i,&\ell=j,\\\ell,&\ell\ne j.\end{cases}$$

This finite binary lookdown is also consistent under restriction to the first $n$ levels: arrows targeted above $n$ do nothing there, and parents are always lower. Its total reproduction-clock rate is $\binom N2$, so the finite-type graphical process is nonexplosive. The occupied ancestral levels need not form a prefix. An arrow from an unoccupied lower level into an occupied level moves an ancestral block without merging any blocks.

Nevertheless, every pair of distinct ancestral blocks at occupied levels $i<j$ merges through exactly its rate-one $i\to j$ clock. All other arrows either leave the partition unchanged or only relocate a block. On the finite augmented state space recording ancestral positions, the total rate into each specified pair-merge partition is one, independently of the positions. This is the finite-CTMC lumpability criterion, and gives the same partition generator $Q_n$ and singleton initial state. Hence the two conventions have the same partition-valued genealogy **in law**, with the same right-continuous backward-time convention.

This is not identity of their ancestral positions, type paths, or partition paths under identical arrows. For example, start three ancestral labels at levels $(1,2,3)$ and cross two arrows $1\to2$ backward. The shifting construction gives $(1,1,2)$ and then $(1,1,1)$; the non-shifting construction gives $(1,1,3)$ twice. Their partition laws agree, but this common-clock coupling does not identify the paths.

Multiplying all binary clock rates by $c\ge0$ multiplies the partition generator by $c$. Thus the pure Kingman measure $\Lambda=c\delta_0$ gives rate $c$ per block pair, rate zero for larger mergers, and a constant genealogy when $c=0$. In particular $\Lambda=\delta_0$ gives the required Kingman bridge. This scaling assertion does not cover a measure with mass on $(0,1]$.

## Depends on

- [Finite-level lookdown process: consistency, exchangeability and fixed-time sampling](../../population-genetics/diffusion-theory/fleming-viot-processes/finite-level-lookdown-process-and-projective-con.md)
- [Rate matrix of Kingman's partition-valued coalescent](../partition-valued-kingman-coalescent/partition-rate.md)

## Residual scope

The general non-shifting $\Lambda$ construction, its finite-rate thinning of impact events, and the rate of each prescribed $k$-block merger remain outside this statement. In particular, the two-lineage rate $\Lambda([0,1])$ for general $\Lambda$, the full $\lambda_{b,k}$ formula, and general-$\Lambda$ projective consistency are not discharged by the pure Kingman case. Infinite-level path construction and measure-valued limits are also excluded. The remaining obligation is to identify these graphical genealogies with the continuous-time Markov chain law of the Kingman rate matrix. The related lookdown overview covers this genealogical scope.

## Sources

- M. Birkner, *Stochastic population models*, lecture notes, Johannes Gutenberg-Universität Mainz, 2025/26, <https://www.staff.uni-mainz.de/birkner/SPM2526/StochPopModels_25-26.pdf>, Sec. 1.5, Remark 1.5.3 and (1.35), including its explicit left-continuous backward-time convention.
- A. Etheridge, *Diffusion process models in mathematical genetics*, lecture notes, Definition 2.1, Remark 2.2 and the following discussion of the first-$n$ genealogy. The explicit parent-map/lumpability comparison above is a finite-state derivation connecting the two conventions.
