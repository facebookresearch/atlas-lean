# Restriction to a finite sample does not increase VC dimension

Let $C$ be a binary concept class on $\alpha$ with finite VC dimension (the sizes of finite sets shattered by $C$ are bounded above), and let $s \subseteq \alpha$ be a finite sample. Then the VC dimension of the trace family $C|_s$, the largest size of a subset of $s$ it shatters, is at most the VC dimension of $C$:

$$\mathrm{VC}(C|_s) \le \mathrm{VC}(C).$$

The finiteness hypothesis matters because the VC dimension of $C$ is defined as the supremum in $\mathbb{N}$ of shattered sizes, which is $0$ when they are unbounded.
