# Rank-1 constraint systems

A *rank-1 constraint system (R1CS) structure* over a finite field $\mathbb{F}$ is a tuple $(m,n,\ell,A,B,C)$ with $A,B,C\in\mathbb{F}^{m\times n}$ and $n>\ell$. An *instance* is $x\in\mathbb{F}^{\ell}$ and a *witness* is $W\in\mathbb{F}^{n-\ell-1}$. With $z=(W,1,x)\in\mathbb{F}^{n}$, the pair is satisfying iff

$$
(Az)\circ(Bz)=Cz,
$$

where $\circ$ is the entrywise (Hadamard) product. Every arithmetic circuit with $m$ multiplication gates and $n$ wires is expressed by an R1CS with $m$ constraints and $n$ variables, so R1CS satisfiability is NP-complete.

## Sources

- Abhiram Kothapalli, Srinath Setty, Ioanna Tzialla, "Nova: Recursive Zero-Knowledge Arguments from Folding Schemes", CRYPTO (2022), IACR ePrint 2021/370.
- Srinath Setty, "Spartan: Efficient and General-Purpose zkSNARKs without Trusted Setup", CRYPTO (2020), IACR ePrint 2019/550.
