# Control reachability of phaser programs is undecidable

Phasers are barriers to which dynamically spawned tasks register and on which they signal and wait. For programs that may spawn unboundedly many tasks and create unboundedly many phasers, it is undecidable whether a configuration with given control locations and Boolean values is reachable.

**Phaser programs.** A phaser program has finitely many shared Boolean variables and finitely many task definitions $T(v_1, \dots, v_k)\{s\}$ with phaser-variable parameters, including a task $\mathtt{main}$. Statements are: $v = \mathtt{newPhaser}()$ (create a phaser and register the current task to it with wait and signal values $0$), $\mathtt{asynch}(T, v_1, \dots, v_k)$ (spawn an instance of $T$, registered to the phasers referenced by the distinct variables $v_1, \dots, v_k$ with the spawner's current values), $\mathtt{drop}(v)$ (deregister), $\mathtt{signal}(v)$ (increment the task's signal value on the phaser), $\mathtt{wait}(v)$ (block until the task's wait value on the phaser is smaller than the signal value of every task registered to it), $\mathtt{next}(v)$ (signal then wait), the atomic barrier block $\mathtt{next}(v)\{s\}$, Boolean assignments and assertions over conditions built from variables, constants and nondeterministic choice, $\mathtt{while}$ loops, sequencing and $\mathtt{exit}$. Execution starts with one instance of $\mathtt{main}$; task instances interleave. A program is *non-atomic* if it does not use $\mathtt{next}(v)\{s\}$. A *control partial configuration* fixes the values of some Boolean variables and the control sequences of some task instances and their registrations, without constraining the wait and signal values.

**Theorem (Ganjei, Rezine, Henrio, Eles and Peng).** The following problem is undecidable: given a phaser program and a control partial configuration, is some configuration that includes it (up to renaming of task instances and phasers) reachable from the initial configuration?

The program is part of the input; executions may create arbitrarily many task instances and phasers. The paper proves further limits, each by a reduction from two-counter machines: control reachability stays undecidable when only executions whose configurations have at most $K$ phasers referenced by task variables are considered ($K$-control-reachability; the proof uses $K = 4$), and for programs generating finitely many phasers when atomic blocks $\mathtt{next}(v)\{s\}$ are allowed; plain reachability, which also constrains wait and signal values, is undecidable for non-atomic programs generating finitely many phasers when the gaps between those values are not bounded.

## Depends on

None.

## Proof depends on

- [Two-counter machines are universal](../../../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The reduction encodes state reachability of a two-counter Minsky machine. The program has tasks $\mathtt{main}$, $\mathtt{xUnit}$ and $\mathtt{yUnit}$; Boolean variables hold the machine state and pass information between task instances. Each counter is a chain that alternates phasers and task instances, and its value is the length of the chain. Increments extend a chain, decrements shorten it and zero tests inspect its end, using signals and waits along the chain. The final machine state is reachable exactly when a configuration whose Boolean variables encode it is reachable, which a control partial configuration expresses.

## Sources

- Zeinab Ganjei, Ahmed Rezine, Ludovic Henrio, Petru Eles and Zebo Peng, "On Reachability in Parameterized Phaser Programs", Tools and Algorithms for the Construction and Analysis of Systems (TACAS 2019), Part I, Lecture Notes in Computer Science 11427, pp. 299–315, Springer, 2019, <https://doi.org/10.1007/978-3-030-17462-0_17>; the language and its semantics in Section 3, the theorem that control reachability is undecidable in general, stated after the definitions of plain and control reachability, and the theorems of Section "Limitations of deciding reachability" of arXiv:1811.07142v3 (the copy read), <https://arxiv.org/abs/1811.07142v3>.
