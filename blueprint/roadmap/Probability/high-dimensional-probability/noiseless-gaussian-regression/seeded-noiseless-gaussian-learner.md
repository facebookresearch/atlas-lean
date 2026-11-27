# Seeded finite-state noiseless Gaussian learner

Fix natural numbers $d,M,T$. The observable rows are an independent $T$-tuple of standard Gaussian vectors in $\mathbb R^d$. For a fixed unit signal $s$, row $x$ is observed together with $\langle x,s\rangle$. The state set is $[2^M]$. Given a seed, an initial action is a Boolean stop bit and a state, a transition at time $t$ takes seed, previous state and the current row/label pair to a new action, and a terminal output at time $t$ is a unit vector determined by the seed and state. A stop bit at time $t$ tags that state with $t$ permanently, including $t=0$ at initialization. An active state after $T$ observations is given terminal tag $T$.

The seed has an arbitrary probability law, independent of rows and of the signal in the sphere-prior experiment. Admissibility means almost-everywhere measurability of initial choice and each time/state output under the seed law, and of each time/state transition under seed law times standard Gaussian row law times real Lebesgue label measure. It separately requires almost-everywhere measurability of the estimate for every fixed signal under seed–row law and jointly under the sphere–(seed–row) product. Sphere law is normalized spherical volume. For radius $\varepsilon$, success is the mass of the event $\arccos\langle\widehat s,s\rangle\le\varepsilon$ in the indicated experiment. The Gaussian-times-Lebesgue reference is not the actual noiseless observation law.

## Sources

- [Pinned source definition](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/NoiselessRegression.lean#L16-L96)
