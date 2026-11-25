# Decorated-LTS bisimulations are exactly strong barbed bisimulations

A relation $R$ on π-calculus processes is a strong bisimulation of the [decorated reduction system](observed-lts.md) if and only if, whenever $P \mathrel{R} Q$:

- every reduction $P \to P'$ is matched by a reduction $Q \to Q'$ with $P' \mathrel{R} Q'$;
- every reduction $Q \to Q'$ is matched by a reduction $P \to P'$ with $P' \mathrel{R} Q'$;
- $P$ and $Q$ have the same [barbs](barb.md).
