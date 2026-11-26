# Completeness of the dummy adversary

In the UC execution experiment (an environment $\mathcal{Z}$, an adversary $\mathcal{A}$ and a protocol, interacting through party and network ports), the *dummy adversary* forwards every query of the environment to the network port and every reply back. For every adversary $\mathcal{A}$ and environment $\mathcal{Z}$, running $\mathcal{A}$ with $\mathcal{Z}$ is the same experiment as running the dummy adversary with the environment $\mathcal{Z}_{\mathcal{A}}$ that internally simulates $\mathcal{A}$. Hence a protocol $\pi$ UC-emulates $\phi$ if and only if there is a simulator for the dummy adversary alone: the black-box simulator $\mathcal{S}_{\mathcal{A}}$, which runs $\mathcal{A}$ against the dummy-adversary simulator, achieves exactly the advantage of the absorbed environment against the dummy adversary. The same holds for adaptive corruptions, with the adaptive dummy adversary that also forwards corruption requests.

## Proof sketch

Absorbing the adversary into the environment is an identity of programs (associativity of machine composition), which also preserves the environment's call budget up to the adversary's.

## Depends on

- [UC emulation](../uc-emulation.md)
- [Interactive machines, linking and the single-token execution model](uc-interactive-machines.md)

## Sources

- Ran Canetti, "Universally Composable Security", Journal of the ACM, 2020.
