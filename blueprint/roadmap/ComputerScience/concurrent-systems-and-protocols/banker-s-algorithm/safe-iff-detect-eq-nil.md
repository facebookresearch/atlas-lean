# Safe iff detect eq nil

A state is safe exactly when the pending list has no repetitions and the
deadlock-detection algorithm, run with the remaining needs as requests, reports
no process.
