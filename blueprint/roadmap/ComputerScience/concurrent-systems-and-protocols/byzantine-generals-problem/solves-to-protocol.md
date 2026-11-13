# `OM(m)` solves the Byzantine generals problem as an oral-message protocol

**`OM(m)` solves the Byzantine generals problem as an oral-message protocol** (Theorem 1 of
Lamport, Shostak and Pease). If there are more than `3 m` generals of a finite type, then
`toProtocol c m` satisfies IC1 and IC2 after `m + 1` rounds, for every order, every set of at most
`m` traitors and every behavior of the traitors.
