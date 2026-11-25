# Arc flow equals arc volume for routes without repeated arcs

For routes given as lists of arcs, none repeating an arc, and route flows $f$, the flow on arc $e$ (the total flow of routes using $e$) equals its volume (the sum over routes of the flow times the number of traversals of $e$). The identity holds for any origin-destination pairs and latencies; without the no-repeat condition it can fail, since the flow counts a repeated arc once.
