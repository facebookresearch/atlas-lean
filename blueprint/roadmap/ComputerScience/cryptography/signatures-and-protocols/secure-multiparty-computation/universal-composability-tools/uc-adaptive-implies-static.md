# Static emulation from adaptive emulation and transitivity of emulation

(i) If $\pi$ UC-emulates $\phi$ against adaptive adversaries (which may corrupt parties during the execution and, in the non-erasing model, learn their whole state), then $\pi$ UC-emulates $\phi$ against static adversaries: clamp a static adversary to its initial corruption set, which preserves its call budget, and observe that the adaptive simulator, run against a clamped adversary, corrupts no new parties. (ii) Emulation is reflexive (every protocol emulates itself with zero error) and transitive: if $\pi_1$ emulates $\pi_2$ with simulator overhead $g_{12}$ and error $\varepsilon_{12}$, and $\pi_2$ emulates $\pi_3$ with $g_{23}$, $\varepsilon_{23}$, then $\pi_1$ emulates $\pi_3$ with overhead $g_{23} \circ g_{12}$ and error $\varepsilon_{12} + \varepsilon_{23}$; the distinguishing advantage is symmetric and satisfies the triangle inequality.

## Proof sketch

(i) The clamped adversary's corruption requests outside the initial set are never issued, so the adaptive execution with it coincides with the static one. (ii) Compose the simulators and apply the triangle inequality.

## Depends on

- [UC emulation](../uc-emulation.md)
- [Adaptive corruptions in UC execution](uc-adaptive-corruptions.md)

## Proof depends on

- [Completeness of the dummy adversary](uc-dummy-adversary.md)

## Sources

- Ran Canetti, "Universally Composable Security", Journal of the ACM, 2020.
