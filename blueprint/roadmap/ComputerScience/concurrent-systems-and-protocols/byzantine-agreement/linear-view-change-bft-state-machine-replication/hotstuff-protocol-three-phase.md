# Chained HotStuff with locking and three-phase commit

In Chained HotStuff (Algorithm 3), time is divided into views with a deterministic leader rotation $\mathrm{leader}(v)$. In view $v$, the leader proposes a block $b^*$ extending the block of the highest QC it knows (its generic QC, updated from the new-view messages), with that QC as $b^*$'s justification. If leaders of intervening views failed to obtain QCs, the proposal first extends that block with blank (dummy) blocks, one per skipped view, so that every block's height equals its view number (Section 5, procedure CREATELEAF); hence a certified block is the direct parent of $b^*$ exactly when it was proposed in view $v - 1$. A replica that receives the proposal checks that it is safe, that is, $b^*$ extends the replica's locked block, or the view of $b^*$'s justifying QC is higher than that of its locked QC, and if so sends its view-$v$ vote (a signature share) to the next leader, $\mathrm{leader}(v+1)$, which combines $n - f$ votes into the QC for $b^*$ (lines 16 and 23–25). Write $b'' $ for the block certified by $b^*$'s QC, $b'$ for the block certified by $b''$'s QC, and $b$ for the block certified by $b'$'s QC. The replica then acts on direct-parent links, where a block's parent is the block it directly extends (lines 17–22): if $b^*.\mathrm{parent} = b''$, it adopts $b^*$'s justifying QC as its generic QC; if moreover $b''.\mathrm{parent} = b'$, it locks on $b''$'s justifying QC (the QC for $b'$); and if moreover $b'.\mathrm{parent} = b$, it commits $b$ and its ancestors. A commit thus requires an observed three-chain of direct-parent certificate links, that is, blocks $b, b', b'', b^*$ proposed in four consecutive views, not merely the existence of three certificates. On a view-change interrupt, a replica sends its generic QC to $\mathrm{leader}(v+1)$, which proceeds after receiving $n - f$ messages without any further view-change subprotocol.

## Depends on

- [Quorum certificate from threshold signatures](quorum-certificate-threshold-signatures.md)
- [Byzantine fault-tolerant state machine replication under partial synchrony](byzantine-state-machine-replication.md)

## Sources

- M. Yin, D. Malkhi, M. K. Reiter, G. Golan Gueta, I. Abraham, "HotStuff: BFT Consensus with Linearity and Responsiveness", PODC 2019, arXiv:1803.05069, Section 5 (Algorithm 3).
