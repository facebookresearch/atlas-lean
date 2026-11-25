# The ancestral selection graph line count as a non-explosive chain

Fix $\sigma\ge0$. Use the [Wright–Fisher convention](../wright-fisher-diffusion/generator.md) $L_\sigma f=\tfrac12x(1-x)f''+\sigma x(1-x)f'$, without mutation. The ancestral selection graph line count is the minimal Markov jump process on $\mathbb N_0$ with birth rate $b_n=\sigma n$, death rate $d_n=\binom n2$, and total exit rate $q_n=b_n+d_n$. The positive integers form a closed class. State zero is an absorbing extension for the zeroth moment; state one is absorbing only when $\sigma=0$.

## Construction and generator

At a state with $q_n>0$, wait an exponential time of rate $q_n$, then jump to $n+1$ with probability $b_n/q_n$ and to $n-1$ with probability $d_n/q_n$. Use independent unit exponential and uniform variables for successive holding times and jump choices. If $q_n=0$, stay at $n$ forever; do not divide by zero. Until the possible accumulation time of its jumps this defines the minimal process, with a cemetery state after explosion if necessary.

All exit rates are finite, the off-diagonal rates are nonnegative and each row of the rate matrix $Q$ sums to zero. For a finitely supported real $f$, the infinitesimal generator is

$$\lim_{t\downarrow0}\frac{\mathbb E_n[f(N_t)]-f(n)}t=b_n\bigl(f(n+1)-f(n)\bigr)+d_n\bigl(f(n-1)-f(n)\bigr)=(A_\sigma f)(n),$$

with the predecessor of zero interpreted as zero. Thus it realizes the [ASG generator](asg-generator.md). Its identification with the diffusion on the moment functions is the [operator duality](generator-one-sub-pow-eq-asg-generator.md), not a new polynomial identity. When $\sigma>0$ the process is **not stopped at its first visit to one**: another branching occurs there at rate $\sigma$.

## Explicit non-explosion proof

Start at a finite $n$ and let $M>n$ be an integer. Write $\tau_M=\inf\{t:N_t=M\}$, with value infinity if the level is never reached. Before $\tau_M$ the chain lies in a finite set with bounded exit rates; the stopped process is a finite-state chain. For $V(j)=j$, its drift before stopping is

$$(A_\sigma V)(j)=\sigma j-\frac{j(j-1)}2\le\sigma V(j).$$

The finite-state stopped Dynkin formula gives, for $g_M(t)=\mathbb E_n[N_{t\wedge\tau_M}]$,

$$g_M(t)\le n+\sigma\int_0^t g_M(s)\,ds,\qquad g_M(t)\le n e^{\sigma t}.$$

The second inequality is Grönwall's inequality. Because the jumps have size one, $N_{\tau_M}=M$ on a hit. Consequently

$$\mathbb P_n(\tau_M\le T)\le\frac{n e^{\sigma T}}M\longrightarrow0\qquad(M\to\infty)$$

for each finite $T\ge0$. An explosion cannot occur while the process stays in a fixed finite set, since the exit rates there are bounded. It would therefore require hitting every level before time $T$, an event of probability zero by this estimate. The minimal chain is non-explosive. This argument uses $V$ only on finite stopped chains, not an unproved global generator-domain assumption for an unbounded function. It also works at $\sigma=0$; directly, that case has at most $n-1$ deaths from a positive starting state.

The transition probabilities are therefore conservative, $\sum_m p_t(n,m)=1$, and obey the countable-state backward equation

$$\partial_t p_t(n,m)=\sum_j Q_{nj}p_t(j,m).$$

Each row of this sum has at most three nonzero terms. The jump-chain construction and non-explosion identify the unique standard conservative Markov jump law with these rates and initial state. They do not follow merely from a finite-state matrix-exponential theorem applied to an infinite matrix.

## Depends on

- [Generator of the ancestral selection graph line-counting process](asg-generator.md)

## Related

- [Selection duality in operator form](generator-one-sub-pow-eq-asg-generator.md)

## Scope

A proof page must still supply the construction of the jump process, the stopped estimate and the countable-state chain framework. The operator and stationary-weight identities are the linked statements; the full branching graph with labeled ancestral lines is not constructed here.

## Sources

- M. Birkner, *Stochastic population models*, 2025/26, <https://www.staff.uni-mainz.de/birkner/SPM2526/StochPopModels_25-26.pdf>, Section 3.4.1, Observations 3.4.5–3.4.6. Set both mutation rates to zero. Birkner's per-line branching rate is $\sigma_B/2$, so **$\sigma_B=2\sigma$** in this page's convention; pairwise coalescence has rate one in both conventions. The stopped non-explosion proof above is an explicit derivation.
