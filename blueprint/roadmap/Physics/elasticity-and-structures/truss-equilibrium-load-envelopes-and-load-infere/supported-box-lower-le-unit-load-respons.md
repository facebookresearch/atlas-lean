# Supported box Lower le unit Load Response

Supported lower box bound: for the fixed output `aout`, every
supported pattern load in the box `0 ≤ f i ≤ cap i` over the free
coordinates has unit-load response at least the lower envelope
value at the exported influence vector. The influence coordinates
are those of the one vector `Mechanics.TrussCompatibility.influenceVector r a b S k aout`; no
further inverse is formed and no solve reading of the response is
used.
