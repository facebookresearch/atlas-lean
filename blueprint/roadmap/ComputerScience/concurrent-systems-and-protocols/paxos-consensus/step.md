# One step of single-decree Paxos

The transitions of single-decree Paxos, one per [action](action.md), for a [quorum system](quorum-system.md):

- **prepare $n$:** the prepare request $n$ is sent (Phase 1(a)).
- **promise $a$, $n$, $r$:** if the prepare request $n$ was sent, acceptor $a$ has responded to no prepare request numbered $n$ or more, and $r$ is the [highest-numbered acceptance](highest-below.md) of $a$ below $n$, then $a$ records $n$ as its highest prepare number and sends the response $(a, n, r)$ (Phase 1(b)).
- **propose $n$, $v$, $S$:** if no proposal numbered $n$ was issued, $S$ is a quorum, every acceptor of $S$ has responded to the prepare request $n$, and $v$ satisfies [Lamport's value rule](safe-value.md) for those responses, then the proposal $(n, v)$ is issued (Phase 2(a)).
- **accept $a$, $n$, $v$:** if the proposal $(n, v)$ was issued and acceptor $a$ has responded to no prepare request numbered greater than $n$ (rule P1a), then $a$ accepts it (Phase 2(b)).

Messages are never removed, so any of them may be used later, repeatedly, or never. Crashes and restarts change no state: acceptors keep their state in stable storage and proposers hold none.

## Sources

- L. Lamport, *Paxos Made Simple*, ACM SIGACT News 32(4), December 2001, 51–58; author's version dated 01 Nov 2001: Section 2.2, P1a and Phases 1 and 2.
