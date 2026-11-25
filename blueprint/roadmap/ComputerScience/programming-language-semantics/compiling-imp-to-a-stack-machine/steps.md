# Multi-step execution of the stack machine

For a program $P$, the multi-step relation on
configurations is the reflexive transitive closure of the step relation of the stack machine
running $P$: it relates $c$ to $c'$ when $c'$ is obtained from $c$ by zero or more steps.
