# When a philosopher can move

Given a protocol and a state, philosopher $i$ can move
exactly when it is thinking (phase $0$) and its first fork is not held by any philosopher, or it
holds its first fork (phase $1$) and its second fork is not held by any philosopher, or it is
eating (phase $2$), in which case its move puts both forks down.
