# Message complexity of Chang–Roberts and Peterson ring election

On a unidirectional asynchronous FIFO ring of $n$ processes with distinct identifiers in which all processes initiate, the Chang–Roberts algorithm elects exactly the maximum identifier, terminates, and sends at most $n(n+1)/2$ messages; averaged over all cyclic arrangements of identifiers it sends exactly $n H_n$ messages, where $H_n$ is the $n$-th harmonic number. Peterson's two-hop algorithm, in which active processes compare their temporary identifier with those of the two preceding active processes, at least halves the number of active processes in each phase, elects a unique leader within $\lceil \log_2 n \rceil + 1$ phases, and sends $O(n \log n)$ messages.

## Proof sketch

In Chang–Roberts, the message of identifier $x$ travels until it meets a larger identifier, so total messages are the sum of these arc lengths; averaging over all arrangements, the identifier with $k - 1$ larger ones travels $n/k$ links in expectation, which sums to $n H_n$. In Peterson's algorithm a process survives a phase only if its middle value is a local maximum, and no two consecutive active processes both survive.

## Depends on

- [The Chang–Roberts transition system](../../chang-roberts-leader-election/lts.md)
- [Only the maximum is elected](../../chang-roberts-leader-election/leader-max.md)

## Proof depends on

- [Message complexity of Hirschberg–Sinclair leader election](../../local-distributed-algorithms/message-complexity-of-hirschbergsinclair-leader.md)

## Sources

- Ernest Chang and Rosemary Roberts, "An Improved Algorithm for Decentralized Extrema-Finding in Circular Configurations of Processes", Communications of the ACM, 1979.
- Gary L. Peterson, "An O(n log n) Unidirectional Algorithm for the Circular Extrema Problem", ACM Transactions on Programming Languages and Systems, 1982.
