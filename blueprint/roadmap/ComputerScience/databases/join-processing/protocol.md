# Local functions of a query communication protocol

A protocol fixes three local functions: worker-to-worker send, relation-server-to-worker
send, and worker report. All see the same random seed. A worker sees only its own view; an
input server sees only its own encoded relation. Sender and destination indices are public.
